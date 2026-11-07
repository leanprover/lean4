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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___boxed(lean_object*);
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
size_t v_x_359__boxed_50_; lean_object* v_res_51_; 
v_x_359__boxed_50_ = lean_unbox_usize(v_x_48_);
lean_dec(v_x_48_);
v_res_51_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_47_, v_x_359__boxed_50_, v_x_49_);
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
size_t v_x_464__boxed_102_; lean_object* v_res_103_; 
v_x_464__boxed_102_ = lean_unbox_usize(v_x_100_);
lean_dec(v_x_100_);
v_res_103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_98_, v_x_99_, v_x_464__boxed_102_, v_x_101_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(lean_object* v_self_118_, lean_object* v_type_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; 
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
v___x_125_ = lean_infer_type(v_self_118_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v___x_125_, 1);
v___x_127_ = l_Lean_Meta_isExprDefEq(v_a_126_, v_type_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec_ref(v_type_119_);
v_a_128_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_125_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_125_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0___boxed(lean_object* v_self_136_, lean_object* v_type_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_136_, v_type_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_144_, lean_object* v_n_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___y_152_; lean_object* v_self_169_; lean_object* v___x_170_; uint8_t v_transparency_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
v_self_169_ = lean_ctor_get(v_n_145_, 0);
lean_inc_ref(v_self_169_);
lean_dec_ref(v_n_145_);
v___x_170_ = l_Lean_Meta_Context_config(v_a_146_);
v_transparency_171_ = lean_ctor_get_uint8(v___x_170_, 9);
lean_dec_ref(v___x_170_);
v___x_172_ = 1;
v___x_173_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v_keyedConfig_174_; uint8_t v_trackZetaDelta_175_; lean_object* v_zetaDeltaSet_176_; lean_object* v_lctx_177_; lean_object* v_localInstances_178_; lean_object* v_defEqCtx_x3f_179_; lean_object* v_synthPendingDepth_180_; lean_object* v_customCanUnfoldPredicate_x3f_181_; uint8_t v_univApprox_182_; uint8_t v_inTypeClassResolution_183_; uint8_t v_cacheInferType_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_keyedConfig_174_ = lean_ctor_get(v_a_146_, 0);
v_trackZetaDelta_175_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*7);
v_zetaDeltaSet_176_ = lean_ctor_get(v_a_146_, 1);
v_lctx_177_ = lean_ctor_get(v_a_146_, 2);
v_localInstances_178_ = lean_ctor_get(v_a_146_, 3);
v_defEqCtx_x3f_179_ = lean_ctor_get(v_a_146_, 4);
v_synthPendingDepth_180_ = lean_ctor_get(v_a_146_, 5);
v_customCanUnfoldPredicate_x3f_181_ = lean_ctor_get(v_a_146_, 6);
v_univApprox_182_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_183_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*7 + 2);
v_cacheInferType_184_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_174_);
v___x_185_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_172_, v_keyedConfig_174_);
lean_inc(v_customCanUnfoldPredicate_x3f_181_);
lean_inc(v_synthPendingDepth_180_);
lean_inc(v_defEqCtx_x3f_179_);
lean_inc_ref(v_localInstances_178_);
lean_inc_ref(v_lctx_177_);
lean_inc(v_zetaDeltaSet_176_);
v___x_186_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_zetaDeltaSet_176_);
lean_ctor_set(v___x_186_, 2, v_lctx_177_);
lean_ctor_set(v___x_186_, 3, v_localInstances_178_);
lean_ctor_set(v___x_186_, 4, v_defEqCtx_x3f_179_);
lean_ctor_set(v___x_186_, 5, v_synthPendingDepth_180_);
lean_ctor_set(v___x_186_, 6, v_customCanUnfoldPredicate_x3f_181_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*7, v_trackZetaDelta_175_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*7 + 1, v_univApprox_182_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*7 + 2, v_inTypeClassResolution_183_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*7 + 3, v_cacheInferType_184_);
lean_inc(v_a_149_);
lean_inc_ref(v_a_148_);
lean_inc(v_a_147_);
v___x_187_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_169_, v_type_144_, v___x_186_, v_a_147_, v_a_148_, v_a_149_);
v___y_152_ = v___x_187_;
goto v___jp_151_;
}
else
{
lean_object* v___x_188_; 
lean_inc(v_a_149_);
lean_inc_ref(v_a_148_);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
v___x_188_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_169_, v_type_144_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
v___y_152_ = v___x_188_;
goto v___jp_151_;
}
v___jp_151_:
{
if (lean_obj_tag(v___y_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_153_ = lean_ctor_get(v___y_152_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___y_152_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___y_152_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___y_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___y_152_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___y_152_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___y_152_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___y_152_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_189_, lean_object* v_n_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_189_, v_n_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = l_Lean_Expr_cleanupAnnotations(v_e_208_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_dec_ref(v___x_209_);
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_213_ = l_Lean_Expr_isApp(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v___x_212_);
lean_dec_ref(v___x_209_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_212_);
lean_dec_ref(v___x_212_);
v___x_216_ = l_Lean_Expr_isApp(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v___x_215_);
lean_dec_ref(v___x_209_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_215_);
lean_dec_ref(v___x_215_);
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_220_ = l_Lean_Expr_isConstOf(v___x_218_, v___x_219_);
lean_dec_ref(v___x_218_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec_ref(v___x_209_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_arg_222_; lean_object* v___x_223_; 
v_arg_222_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_arg_222_);
lean_dec_ref(v___x_209_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_arg_222_);
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___boxed(lean_object* v_e_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_e_224_);
lean_dec_ref(v_e_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Rat_ofInt(v_a_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_nat_to_int(v_a_228_);
v___x_230_ = l_Rat_ofInt(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_key_234_; lean_object* v_value_235_; lean_object* v_tail_236_; uint8_t v___x_237_; 
v_key_234_ = lean_ctor_get(v_x_232_, 0);
v_value_235_ = lean_ctor_get(v_x_232_, 1);
v_tail_236_ = lean_ctor_get(v_x_232_, 2);
v___x_237_ = lean_expr_eqv(v_key_234_, v_a_231_);
if (v___x_237_ == 0)
{
v_x_232_ = v_tail_236_;
goto _start;
}
else
{
lean_object* v___x_239_; 
lean_inc(v_value_235_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_value_235_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_240_, v_x_241_);
lean_dec(v_x_241_);
lean_dec_ref(v_a_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_buckets_245_; lean_object* v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v_fold_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_buckets_245_ = lean_ctor_get(v_m_243_, 1);
v___x_246_ = lean_array_get_size(v_buckets_245_);
v___x_247_ = l_Lean_Expr_hash(v_a_244_);
v___x_248_ = 32ULL;
v___x_249_ = lean_uint64_shift_right(v___x_247_, v___x_248_);
v_fold_250_ = lean_uint64_xor(v___x_247_, v___x_249_);
v___x_251_ = 16ULL;
v___x_252_ = lean_uint64_shift_right(v_fold_250_, v___x_251_);
v___x_253_ = lean_uint64_xor(v_fold_250_, v___x_252_);
v___x_254_ = lean_uint64_to_usize(v___x_253_);
v___x_255_ = lean_usize_of_nat(v___x_246_);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_sub(v___x_255_, v___x_256_);
v___x_258_ = lean_usize_land(v___x_254_, v___x_257_);
v___x_259_ = lean_array_uget_borrowed(v_buckets_245_, v___x_258_);
v___x_260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_244_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_261_, v_a_262_);
lean_dec_ref(v_a_262_);
lean_dec_ref(v_m_261_);
return v_res_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_303_, lean_object* v_model_304_, lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_304_, v_e_305_);
if (lean_obj_tag(v___x_314_) == 1)
{
lean_object* v___x_315_; 
lean_dec_ref(v_e_305_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; 
lean_dec(v___x_314_);
v___x_316_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_305_, v_a_307_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_579_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_579_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_579_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_579_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_cleanupAnnotations(v_a_317_);
lean_dec(v_a_317_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_321_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_324_ = l_Lean_Expr_isApp(v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_323_);
lean_dec_ref(v___x_321_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_arg_325_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_325_);
lean_dec_ref(v___x_321_);
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_323_);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_329_ == 0)
{
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v___x_323_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_arg_330_ = lean_ctor_get(v___x_323_, 1);
lean_inc_ref(v_arg_330_);
lean_dec_ref(v___x_323_);
v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_333_ = l_Lean_Expr_isConstOf(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_335_ = l_Lean_Expr_isConstOf(v___x_331_, v___x_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; 
v___x_336_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v_arg_330_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
lean_dec_ref(v___x_331_);
v___x_338_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_330_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
lean_dec_ref(v___x_337_);
v___x_340_ = l_Lean_Expr_isApp(v___x_339_);
if (v___x_340_ == 0)
{
lean_dec_ref(v___x_339_);
lean_dec_ref(v_arg_330_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_arg_341_ = lean_ctor_get(v___x_326_, 1);
lean_inc_ref(v_arg_341_);
lean_dec_ref(v___x_326_);
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_339_);
lean_dec_ref(v___x_339_);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_349_);
lean_dec_ref(v___x_342_);
if (v___x_350_ == 0)
{
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_330_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_319_);
goto v___jp_311_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_303_, v_arg_341_);
lean_dec_ref(v_arg_341_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec_ref(v_arg_330_);
lean_dec_ref(v_arg_325_);
v___x_352_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_352_);
v___x_354_ = v___x_319_;
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
else
{
lean_object* v___x_356_; 
lean_del_object(v___x_319_);
v___x_356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
if (lean_obj_tag(v_a_357_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_356_;
}
else
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_inc_ref(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v_val_358_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v_a_357_, 1);
v___x_359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
if (lean_obj_tag(v_a_360_) == 0)
{
lean_dec(v_val_358_);
return v___x_359_;
}
else
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_376_; 
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_377_);
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
else
{
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_376_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_val_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
v_val_364_ = lean_ctor_get(v_a_360_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_375_ == 0)
{
v___x_366_ = v_a_360_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_val_364_);
lean_dec(v_a_360_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = l_Rat_add(v_val_358_, v_val_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_370_);
v___x_372_ = v___x_362_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
else
{
lean_dec(v_val_358_);
return v___x_359_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_356_;
}
}
}
}
else
{
uint8_t v___x_378_; 
lean_dec_ref(v___x_342_);
v___x_378_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_303_, v_arg_341_);
lean_dec_ref(v_arg_341_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec_ref(v_arg_330_);
lean_dec_ref(v_arg_325_);
v___x_379_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_379_);
v___x_381_ = v___x_319_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_383_; 
lean_del_object(v___x_319_);
v___x_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
if (lean_obj_tag(v_a_384_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_383_;
}
else
{
lean_object* v_val_385_; lean_object* v___x_386_; 
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v_val_385_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v_a_384_, 1);
v___x_386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
if (lean_obj_tag(v_a_387_) == 0)
{
lean_dec(v_val_385_);
return v___x_386_;
}
else
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_403_; 
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_404_);
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
else
{
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_402_; 
v_val_391_ = lean_ctor_get(v_a_387_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_402_ == 0)
{
v___x_393_ = v_a_387_;
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v_a_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = l_Rat_sub(v_val_385_, v_val_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_401_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_397_);
v___x_399_ = v___x_389_;
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
}
}
}
}
else
{
lean_dec(v_val_385_);
return v___x_386_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_383_;
}
}
}
}
else
{
uint8_t v___x_405_; 
lean_dec_ref(v___x_342_);
v___x_405_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_303_, v_arg_341_);
lean_dec_ref(v_arg_341_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
lean_dec_ref(v_arg_330_);
lean_dec_ref(v_arg_325_);
v___x_406_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_406_);
v___x_408_ = v___x_319_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
lean_object* v___x_410_; 
lean_del_object(v___x_319_);
v___x_410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
if (lean_obj_tag(v_a_411_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_410_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_413_; 
lean_inc_ref(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v_val_412_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v_a_411_, 1);
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
if (lean_obj_tag(v_a_414_) == 0)
{
lean_dec(v_val_412_);
return v___x_413_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_430_; 
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_413_, 0);
lean_dec(v_unused_431_);
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_430_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_430_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_val_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
v_val_418_ = lean_ctor_get(v_a_414_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_a_414_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v_a_414_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_val_418_);
lean_dec(v_a_414_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = l_Rat_mul(v_val_412_, v_val_418_);
lean_dec(v_val_412_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_424_);
v___x_426_ = v___x_416_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
else
{
lean_dec(v_val_412_);
return v___x_413_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_410_;
}
}
}
}
else
{
uint8_t v___x_432_; 
lean_dec_ref(v___x_342_);
v___x_432_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_303_, v_arg_341_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_303_, v_arg_341_);
lean_dec_ref(v_arg_341_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec_ref(v_arg_330_);
lean_dec_ref(v_arg_325_);
v___x_434_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_434_);
v___x_436_ = v___x_319_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_438_; 
lean_del_object(v___x_319_);
v___x_438_ = l_Lean_Meta_getNatValue_x3f(v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_arg_330_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_468_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_468_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_468_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_468_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
if (lean_obj_tag(v_a_439_) == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec_ref(v_arg_325_);
v___x_443_ = lean_box(0);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_445_ = v___x_441_;
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
else
{
lean_object* v_val_447_; lean_object* v___x_448_; 
lean_del_object(v___x_441_);
v_val_447_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_439_, 1);
v___x_448_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
if (lean_obj_tag(v_a_449_) == 0)
{
lean_dec(v_val_447_);
return v___x_448_;
}
else
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_466_; 
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___x_448_, 0);
lean_dec(v_unused_467_);
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_465_; 
v_val_453_ = lean_ctor_get(v_a_449_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_465_ == 0)
{
v___x_455_ = v_a_449_;
v_isShared_456_ = v_isSharedCheck_465_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v_a_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_465_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_447_);
v___x_458_ = l_Rat_mul(v___x_457_, v_val_453_);
lean_dec_ref(v___x_457_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_460_);
v___x_462_ = v___x_451_;
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
}
}
else
{
lean_dec(v_val_447_);
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_arg_325_);
v_a_469_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_438_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_438_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_319_);
v___x_477_ = l_Lean_Meta_getIntValue_x3f(v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_507_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_507_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
if (lean_obj_tag(v_a_478_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec_ref(v_arg_325_);
v___x_482_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_del_object(v___x_480_);
v_val_486_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_a_478_, 1);
v___x_487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
if (lean_obj_tag(v_a_488_) == 0)
{
lean_dec(v_val_486_);
return v___x_487_;
}
else
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_487_, 0);
lean_dec(v_unused_506_);
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
else
{
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_val_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_504_; 
v_val_492_ = lean_ctor_get(v_a_488_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_504_ == 0)
{
v___x_494_ = v_a_488_;
v_isShared_495_ = v_isSharedCheck_504_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_val_492_);
lean_dec(v_a_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_504_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = l_Rat_ofInt(v_val_486_);
v___x_497_ = l_Rat_mul(v___x_496_, v_val_492_);
lean_dec_ref(v___x_496_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_497_);
v___x_499_ = v___x_494_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_499_);
v___x_501_ = v___x_490_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
else
{
lean_dec(v_val_486_);
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_arg_325_);
v_a_508_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_477_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_477_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
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
uint8_t v___x_516_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v___x_326_);
v___x_516_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_303_, v_arg_330_);
lean_dec_ref(v_arg_330_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec_ref(v_arg_325_);
v___x_517_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_517_);
v___x_519_ = v___x_319_;
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
else
{
lean_object* v___x_521_; 
lean_del_object(v___x_319_);
v___x_521_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_303_, v_model_304_, v_arg_325_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
if (lean_obj_tag(v_a_522_) == 0)
{
return v___x_521_;
}
else
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_538_; 
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_539_);
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_538_;
goto v_resetjp_523_;
}
else
{
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_538_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_537_; 
v_val_526_ = lean_ctor_get(v_a_522_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_a_522_);
if (v_isSharedCheck_537_ == 0)
{
v___x_528_ = v_a_522_;
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_a_522_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_537_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Rat_neg(v_val_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_532_);
v___x_534_ = v___x_524_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
else
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_319_);
v___x_540_ = l_Lean_Meta_getNatValue_x3f(v_arg_330_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_arg_330_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_561_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_561_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_561_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_561_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
if (lean_obj_tag(v_a_541_) == 0)
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_560_; 
v_val_549_ = lean_ctor_get(v_a_541_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_560_ == 0)
{
v___x_551_ = v_a_541_;
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v_a_541_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_555_);
v___x_557_ = v___x_543_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_a_562_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_540_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_540_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
else
{
uint8_t v___x_570_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_323_);
v___x_570_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_303_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_box(0);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_571_);
v___x_573_ = v___x_319_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_575_);
v___x_577_ = v___x_319_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_a_580_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_316_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_316_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_588_, lean_object* v_model_589_, lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_588_, v_model_589_, v_e_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec_ref(v_model_589_);
lean_dec_ref(v_s_588_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_598_, v_a_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_601_, v_m_602_, v_a_603_);
lean_dec_ref(v_a_603_);
lean_dec_ref(v_m_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_nat_to_int(v_a_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_607_, lean_object* v_a_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_608_, v_x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_611_, lean_object* v_a_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_611_, v_a_612_, v_x_613_);
lean_dec(v_x_613_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_615_, lean_object* v_s_616_, lean_object* v_model_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_616_, v_model_617_, v_e_615_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_624_, lean_object* v_s_625_, lean_object* v_model_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_624_, v_s_625_, v_model_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec_ref(v_model_626_);
lean_dec_ref(v_s_625_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_tail_637_; uint8_t v___x_638_; 
v_key_636_ = lean_ctor_get(v_x_634_, 0);
v_tail_637_ = lean_ctor_get(v_x_634_, 2);
v___x_638_ = lean_expr_eqv(v_key_636_, v_a_633_);
if (v___x_638_ == 0)
{
v_x_634_ = v_tail_637_;
goto _start;
}
else
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_640_, lean_object* v_x_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_640_, v_x_641_);
lean_dec(v_x_641_);
lean_dec_ref(v_a_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_buckets_646_; lean_object* v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v_fold_651_; uint64_t v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_buckets_646_ = lean_ctor_get(v_m_644_, 1);
v___x_647_ = lean_array_get_size(v_buckets_646_);
v___x_648_ = l_Lean_Expr_hash(v_a_645_);
v___x_649_ = 32ULL;
v___x_650_ = lean_uint64_shift_right(v___x_648_, v___x_649_);
v_fold_651_ = lean_uint64_xor(v___x_648_, v___x_650_);
v___x_652_ = 16ULL;
v___x_653_ = lean_uint64_shift_right(v_fold_651_, v___x_652_);
v___x_654_ = lean_uint64_xor(v_fold_651_, v___x_653_);
v___x_655_ = lean_uint64_to_usize(v___x_654_);
v___x_656_ = lean_usize_of_nat(v___x_647_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_sub(v___x_656_, v___x_657_);
v___x_659_ = lean_usize_land(v___x_655_, v___x_658_);
v___x_660_ = lean_array_uget_borrowed(v_buckets_646_, v___x_659_);
v___x_661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_645_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_662_, lean_object* v_a_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_662_, v_a_663_);
lean_dec_ref(v_a_663_);
lean_dec_ref(v_m_662_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v_structId_666_, lean_object* v___x_667_, lean_object* v_goal_668_, lean_object* v_as_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_b_672_);
return v___x_679_;
}
else
{
lean_object* v_snd_680_; lean_object* v_a_681_; lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_710_; 
v_snd_680_ = lean_ctor_get(v_b_672_, 1);
lean_inc(v_snd_680_);
lean_dec_ref(v_b_672_);
v_a_681_ = lean_array_uget(v_as_669_, v_i_671_);
v_fst_682_ = lean_ctor_get(v_a_681_, 0);
v_snd_683_ = lean_ctor_get(v_a_681_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_710_ == 0)
{
v___x_685_ = v_a_681_;
v_isShared_686_ = v_isSharedCheck_710_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
lean_dec(v_a_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_710_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v_a_689_; uint8_t v___x_696_; 
v___x_687_ = lean_box(0);
v___x_696_ = lean_nat_dec_eq(v_structId_666_, v_snd_683_);
lean_dec(v_snd_683_);
if (v___x_696_ == 0)
{
lean_dec(v_fst_682_);
v_a_689_ = v_snd_680_;
goto v___jp_688_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_680_, v_fst_682_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_inc(v_fst_682_);
v___x_698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_667_, v_snd_680_, v_fst_682_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
if (lean_obj_tag(v_a_699_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_701_; 
v_val_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_a_699_, 1);
v___x_701_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_668_, v_fst_682_, v_val_700_, v_snd_680_);
v_a_689_ = v___x_701_;
goto v___jp_688_;
}
else
{
lean_dec(v_a_699_);
lean_dec(v_fst_682_);
v_a_689_ = v_snd_680_;
goto v___jp_688_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_del_object(v___x_685_);
lean_dec(v_fst_682_);
lean_dec(v_snd_680_);
v_a_702_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_698_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_698_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_dec(v_fst_682_);
v_a_689_ = v_snd_680_;
goto v___jp_688_;
}
}
v___jp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_a_689_);
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_671_, v___x_692_);
v_i_671_ = v___x_693_;
v_b_672_ = v___x_691_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_structId_711_, lean_object* v___x_712_, lean_object* v_goal_713_, lean_object* v_as_714_, lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_724_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_711_, v___x_712_, v_goal_713_, v_as_714_, v_sz_boxed_723_, v_i_boxed_724_, v_b_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec_ref(v_as_714_);
lean_dec_ref(v_goal_713_);
lean_dec_ref(v___x_712_);
lean_dec(v_structId_711_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v_structId_726_, lean_object* v___x_727_, lean_object* v_goal_728_, lean_object* v_as_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
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
lean_object* v_snd_740_; lean_object* v_a_741_; lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_770_; 
v_snd_740_ = lean_ctor_get(v_b_732_, 1);
lean_inc(v_snd_740_);
lean_dec_ref(v_b_732_);
v_a_741_ = lean_array_uget(v_as_729_, v_i_731_);
v_fst_742_ = lean_ctor_get(v_a_741_, 0);
v_snd_743_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_745_ = v_a_741_;
v_isShared_746_ = v_isSharedCheck_770_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_inc(v_fst_742_);
lean_dec(v_a_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_770_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v_a_749_; uint8_t v___x_756_; 
v___x_747_ = lean_box(0);
v___x_756_ = lean_nat_dec_eq(v_structId_726_, v_snd_743_);
lean_dec(v_snd_743_);
if (v___x_756_ == 0)
{
lean_dec(v_fst_742_);
v_a_749_ = v_snd_740_;
goto v___jp_748_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_740_, v_fst_742_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_inc(v_fst_742_);
v___x_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_727_, v_snd_740_, v_fst_742_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
if (lean_obj_tag(v_a_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_761_; 
v_val_760_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_a_759_, 1);
v___x_761_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_728_, v_fst_742_, v_val_760_, v_snd_740_);
v_a_749_ = v___x_761_;
goto v___jp_748_;
}
else
{
lean_dec(v_a_759_);
lean_dec(v_fst_742_);
v_a_749_ = v_snd_740_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_745_);
lean_dec(v_fst_742_);
lean_dec(v_snd_740_);
v_a_762_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_758_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_758_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_dec(v_fst_742_);
v_a_749_ = v_snd_740_;
goto v___jp_748_;
}
}
v___jp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_a_749_);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_a_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_731_, v___x_752_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_726_, v___x_727_, v_goal_728_, v_as_729_, v_sz_730_, v___x_753_, v___x_751_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v_structId_771_, lean_object* v___x_772_, lean_object* v_goal_773_, lean_object* v_as_774_, lean_object* v_sz_775_, lean_object* v_i_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
size_t v_sz_boxed_783_; size_t v_i_boxed_784_; lean_object* v_res_785_; 
v_sz_boxed_783_ = lean_unbox_usize(v_sz_775_);
lean_dec(v_sz_775_);
v_i_boxed_784_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_771_, v___x_772_, v_goal_773_, v_as_774_, v_sz_boxed_783_, v_i_boxed_784_, v_b_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec_ref(v_as_774_);
lean_dec_ref(v_goal_773_);
lean_dec_ref(v___x_772_);
lean_dec(v_structId_771_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_786_, lean_object* v_structId_787_, lean_object* v___x_788_, lean_object* v_goal_789_, lean_object* v_n_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
if (lean_obj_tag(v_n_790_) == 0)
{
lean_object* v_cs_797_; lean_object* v___x_798_; lean_object* v___x_799_; size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_cs_797_ = lean_ctor_get(v_n_790_, 0);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_b_791_);
v_sz_800_ = lean_array_size(v_cs_797_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_786_, v_structId_787_, v___x_788_, v_goal_789_, v_cs_797_, v_sz_800_, v___x_801_, v___x_799_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_817_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_fst_807_; 
v_fst_807_ = lean_ctor_get(v_a_803_, 0);
if (lean_obj_tag(v_fst_807_) == 0)
{
lean_object* v_snd_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_snd_808_ = lean_ctor_get(v_a_803_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_803_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_snd_808_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_val_813_; lean_object* v___x_815_; 
lean_inc_ref(v_fst_807_);
lean_dec(v_a_803_);
v_val_813_ = lean_ctor_get(v_fst_807_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_fst_807_, 1);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_val_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_802_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_802_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_vs_826_; lean_object* v___x_827_; lean_object* v___x_828_; size_t v_sz_829_; size_t v___x_830_; lean_object* v___x_831_; 
v_vs_826_ = lean_ctor_get(v_n_790_, 0);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_b_791_);
v_sz_829_ = lean_array_size(v_vs_826_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_787_, v___x_788_, v_goal_789_, v_vs_826_, v_sz_829_, v___x_830_, v___x_828_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_846_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_846_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_fst_836_; 
v_fst_836_ = lean_ctor_get(v_a_832_, 0);
if (lean_obj_tag(v_fst_836_) == 0)
{
lean_object* v_snd_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_snd_837_ = lean_ctor_get(v_a_832_, 1);
lean_inc(v_snd_837_);
lean_dec(v_a_832_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_snd_837_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_838_);
v___x_840_ = v___x_834_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; 
lean_inc_ref(v_fst_836_);
lean_dec(v_a_832_);
v_val_842_ = lean_ctor_get(v_fst_836_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v_fst_836_, 1);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v_val_842_);
v___x_844_ = v___x_834_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_val_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_831_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_831_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_855_, lean_object* v_structId_856_, lean_object* v___x_857_, lean_object* v_goal_858_, lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_b_862_);
return v___x_869_;
}
else
{
lean_object* v_snd_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_904_; 
v_snd_870_ = lean_ctor_get(v_b_862_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_b_862_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v_b_862_, 0);
lean_dec(v_unused_905_);
v___x_872_ = v_b_862_;
v_isShared_873_ = v_isSharedCheck_904_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snd_870_);
lean_dec(v_b_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_904_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_876_; 
v___x_874_ = lean_box(0);
v_a_875_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
lean_inc(v_snd_870_);
v___x_876_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_855_, v_structId_856_, v___x_857_, v_goal_858_, v_a_875_, v_snd_870_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_895_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v_a_877_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_881_);
v___x_883_ = v___x_872_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_870_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; 
lean_del_object(v___x_879_);
lean_dec(v_snd_870_);
v_a_888_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v_a_877_, 1);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v_a_888_);
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_890_ = v___x_872_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_a_888_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
size_t v___x_891_; size_t v___x_892_; 
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_861_, v___x_891_);
v_i_861_ = v___x_892_;
v_b_862_ = v___x_890_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_del_object(v___x_872_);
lean_dec(v_snd_870_);
v_a_896_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_876_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_876_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_906_, lean_object* v_structId_907_, lean_object* v___x_908_, lean_object* v_goal_909_, lean_object* v_as_910_, lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_920_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_906_, v_structId_907_, v___x_908_, v_goal_909_, v_as_910_, v_sz_boxed_919_, v_i_boxed_920_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_as_910_);
lean_dec_ref(v_goal_909_);
lean_dec_ref(v___x_908_);
lean_dec(v_structId_907_);
lean_dec_ref(v_init_906_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_922_, lean_object* v_structId_923_, lean_object* v___x_924_, lean_object* v_goal_925_, lean_object* v_n_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_922_, v_structId_923_, v___x_924_, v_goal_925_, v_n_926_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v_n_926_);
lean_dec_ref(v_goal_925_);
lean_dec_ref(v___x_924_);
lean_dec(v_structId_923_);
lean_dec_ref(v_init_922_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v_structId_934_, lean_object* v___x_935_, lean_object* v_goal_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_940_);
return v___x_947_;
}
else
{
lean_object* v_snd_948_; lean_object* v_a_949_; lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_978_; 
v_snd_948_ = lean_ctor_get(v_b_940_, 1);
lean_inc(v_snd_948_);
lean_dec_ref(v_b_940_);
v_a_949_ = lean_array_uget(v_as_937_, v_i_939_);
v_fst_950_ = lean_ctor_get(v_a_949_, 0);
v_snd_951_ = lean_ctor_get(v_a_949_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_978_ == 0)
{
v___x_953_ = v_a_949_;
v_isShared_954_ = v_isSharedCheck_978_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_a_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_978_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_a_957_; uint8_t v___x_964_; 
v___x_955_ = lean_box(0);
v___x_964_ = lean_nat_dec_eq(v_structId_934_, v_snd_951_);
lean_dec(v_snd_951_);
if (v___x_964_ == 0)
{
lean_dec(v_fst_950_);
v_a_957_ = v_snd_948_;
goto v___jp_956_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_948_, v_fst_950_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_inc(v_fst_950_);
v___x_966_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_935_, v_snd_948_, v_fst_950_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
if (lean_obj_tag(v_a_967_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_969_; 
v_val_968_ = lean_ctor_get(v_a_967_, 0);
lean_inc(v_val_968_);
lean_dec_ref_known(v_a_967_, 1);
v___x_969_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_936_, v_fst_950_, v_val_968_, v_snd_948_);
v_a_957_ = v___x_969_;
goto v___jp_956_;
}
else
{
lean_dec(v_a_967_);
lean_dec(v_fst_950_);
v_a_957_ = v_snd_948_;
goto v___jp_956_;
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_del_object(v___x_953_);
lean_dec(v_fst_950_);
lean_dec(v_snd_948_);
v_a_970_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_966_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_966_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_dec(v_fst_950_);
v_a_957_ = v_snd_948_;
goto v___jp_956_;
}
}
v___jp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_a_957_);
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_a_957_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
size_t v___x_960_; size_t v___x_961_; 
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_939_, v___x_960_);
v_i_939_ = v___x_961_;
v_b_940_ = v___x_959_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v_structId_979_, lean_object* v___x_980_, lean_object* v_goal_981_, lean_object* v_as_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
size_t v_sz_boxed_991_; size_t v_i_boxed_992_; lean_object* v_res_993_; 
v_sz_boxed_991_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_992_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_979_, v___x_980_, v_goal_981_, v_as_982_, v_sz_boxed_991_, v_i_boxed_992_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec_ref(v_as_982_);
lean_dec_ref(v_goal_981_);
lean_dec_ref(v___x_980_);
lean_dec(v_structId_979_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v_structId_994_, lean_object* v___x_995_, lean_object* v_goal_996_, lean_object* v_as_997_, size_t v_sz_998_, size_t v_i_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_999_, v_sz_998_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_b_1000_);
return v___x_1007_;
}
else
{
lean_object* v_snd_1008_; lean_object* v_a_1009_; lean_object* v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1038_; 
v_snd_1008_ = lean_ctor_get(v_b_1000_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v_b_1000_);
v_a_1009_ = lean_array_uget(v_as_997_, v_i_999_);
v_fst_1010_ = lean_ctor_get(v_a_1009_, 0);
v_snd_1011_ = lean_ctor_get(v_a_1009_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1013_ = v_a_1009_;
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snd_1011_);
lean_inc(v_fst_1010_);
lean_dec(v_a_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v_a_1017_; uint8_t v___x_1024_; 
v___x_1015_ = lean_box(0);
v___x_1024_ = lean_nat_dec_eq(v_structId_994_, v_snd_1011_);
lean_dec(v_snd_1011_);
if (v___x_1024_ == 0)
{
lean_dec(v_fst_1010_);
v_a_1017_ = v_snd_1008_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_1008_, v_fst_1010_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_inc(v_fst_1010_);
v___x_1026_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_995_, v_snd_1008_, v_fst_1010_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
if (lean_obj_tag(v_a_1027_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1029_; 
v_val_1028_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_val_1028_);
lean_dec_ref_known(v_a_1027_, 1);
v___x_1029_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_996_, v_fst_1010_, v_val_1028_, v_snd_1008_);
v_a_1017_ = v___x_1029_;
goto v___jp_1016_;
}
else
{
lean_dec(v_a_1027_);
lean_dec(v_fst_1010_);
v_a_1017_ = v_snd_1008_;
goto v___jp_1016_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1013_);
lean_dec(v_fst_1010_);
lean_dec(v_snd_1008_);
v_a_1030_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1026_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_dec(v_fst_1010_);
v_a_1017_ = v_snd_1008_;
goto v___jp_1016_;
}
}
v___jp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_a_1017_);
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_a_1017_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_999_, v___x_1020_);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_994_, v___x_995_, v_goal_996_, v_as_997_, v_sz_998_, v___x_1021_, v___x_1019_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v_structId_1039_, lean_object* v___x_1040_, lean_object* v_goal_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
size_t v_sz_boxed_1051_; size_t v_i_boxed_1052_; lean_object* v_res_1053_; 
v_sz_boxed_1051_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1052_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1039_, v___x_1040_, v_goal_1041_, v_as_1042_, v_sz_boxed_1051_, v_i_boxed_1052_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_as_1042_);
lean_dec_ref(v_goal_1041_);
lean_dec_ref(v___x_1040_);
lean_dec(v_structId_1039_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v_structId_1054_, lean_object* v___x_1055_, lean_object* v_goal_1056_, lean_object* v_t_1057_, lean_object* v_init_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_root_1064_; lean_object* v_tail_1065_; lean_object* v___x_1066_; 
v_root_1064_ = lean_ctor_get(v_t_1057_, 0);
v_tail_1065_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_init_1058_);
v___x_1066_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1058_, v_structId_1054_, v___x_1055_, v_goal_1056_, v_root_1064_, v_init_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec_ref(v_init_1058_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1103_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v_a_1067_, 1);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_a_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
lean_del_object(v___x_1069_);
v_a_1075_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v_a_1067_, 1);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_a_1075_);
v_sz_1078_ = lean_array_size(v_tail_1065_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1054_, v___x_1055_, v_goal_1056_, v_tail_1065_, v_sz_1078_, v___x_1079_, v___x_1077_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1094_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1094_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fst_1085_; 
v_fst_1085_ = lean_ctor_get(v_a_1081_, 0);
if (lean_obj_tag(v_fst_1085_) == 0)
{
lean_object* v_snd_1086_; lean_object* v___x_1088_; 
v_snd_1086_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1086_);
lean_dec(v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_snd_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_snd_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v_val_1090_; lean_object* v___x_1092_; 
lean_inc_ref(v_fst_1085_);
lean_dec(v_a_1081_);
v_val_1090_ = lean_ctor_get(v_fst_1085_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_fst_1085_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_val_1090_);
v___x_1092_ = v___x_1083_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_val_1090_);
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
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1080_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1080_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1066_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1066_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v_structId_1112_, lean_object* v___x_1113_, lean_object* v_goal_1114_, lean_object* v_t_1115_, lean_object* v_init_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1112_, v___x_1113_, v_goal_1114_, v_t_1115_, v_init_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec_ref(v_t_1115_);
lean_dec_ref(v_goal_1114_);
lean_dec_ref(v___x_1113_);
lean_dec(v_structId_1112_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1123_, lean_object* v_structId_1124_, lean_object* v_model_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_ref_1131_ = lean_ctor_get(v_a_1128_, 2);
v___x_1132_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1133_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1134_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1133_, v_goal_1123_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_structs_1136_; lean_object* v_exprToStructIdEntries_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v_structs_1136_ = lean_ctor_get(v_a_1135_, 0);
lean_inc_ref(v_structs_1136_);
v_exprToStructIdEntries_1137_ = lean_ctor_get(v_a_1135_, 3);
lean_inc_ref(v_exprToStructIdEntries_1137_);
lean_dec(v_a_1135_);
v___x_1138_ = lean_array_get(v___x_1132_, v_structs_1136_, v_structId_1124_);
lean_dec_ref(v_structs_1136_);
v___x_1139_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1124_, v___x_1138_, v_goal_1123_, v_exprToStructIdEntries_1137_, v_model_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec_ref(v_exprToStructIdEntries_1137_);
lean_dec(v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_model_1125_);
v_a_1140_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1142_ = v___x_1134_;
v_isShared_1143_ = v_isSharedCheck_1151_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1134_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1151_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1144_ = lean_io_error_to_string(v_a_1140_);
v___x_1145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___x_1146_ = l_Lean_MessageData_ofFormat(v___x_1145_);
lean_inc(v_ref_1131_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_ref_1131_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1147_);
v___x_1149_ = v___x_1142_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1152_, lean_object* v_structId_1153_, lean_object* v_model_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1152_, v_structId_1153_, v_model_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_structId_1153_);
lean_dec_ref(v_goal_1152_);
return v_res_1160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1161_, lean_object* v_m_1162_, lean_object* v_a_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1162_, v_a_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1165_, lean_object* v_m_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1165_, v_m_1166_, v_a_1167_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v_m_1166_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1170_, lean_object* v_a_1171_, lean_object* v_x_1172_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1171_, v_x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1174_, lean_object* v_a_1175_, lean_object* v_x_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1174_, v_a_1175_, v_x_1176_);
lean_dec(v_x_1176_);
lean_dec_ref(v_a_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1179_, lean_object* v___x_1180_, lean_object* v_as_1181_, size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_lt(v_i_1183_, v_sz_1182_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v___x_1180_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_b_1184_);
return v___x_1191_;
}
else
{
lean_object* v_snd_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1233_; 
v_snd_1192_ = lean_ctor_get(v_b_1184_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_b_1184_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_b_1184_, 0);
lean_dec(v_unused_1234_);
v___x_1194_ = v_b_1184_;
v_isShared_1195_ = v_isSharedCheck_1233_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snd_1192_);
lean_dec(v_b_1184_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1233_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v_a_1198_; lean_object* v_a_1205_; lean_object* v___x_1206_; 
v___x_1196_ = lean_box(0);
v_a_1205_ = lean_array_uget_borrowed(v_as_1181_, v_i_1183_);
lean_inc(v_a_1205_);
v___x_1206_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1179_, v_a_1205_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; uint8_t v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1207_);
if (v___x_1208_ == 0)
{
lean_dec(v_a_1207_);
v_a_1198_ = v_snd_1192_;
goto v___jp_1197_;
}
else
{
lean_object* v_type_1209_; lean_object* v___x_1210_; 
v_type_1209_ = lean_ctor_get(v___x_1180_, 2);
lean_inc(v_a_1207_);
lean_inc_ref(v_type_1209_);
v___x_1210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1209_, v_a_1207_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; uint8_t v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_dec(v_a_1207_);
v_a_1198_ = v_snd_1192_;
goto v___jp_1197_;
}
else
{
lean_object* v_self_1213_; lean_object* v___x_1214_; 
v_self_1213_ = lean_ctor_get(v_a_1207_, 0);
lean_inc_ref(v_self_1213_);
lean_dec(v_a_1207_);
v___x_1214_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1180_, v_self_1213_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1179_, v_self_1213_, v_val_1215_, v_snd_1192_);
v_a_1198_ = v___x_1216_;
goto v___jp_1197_;
}
else
{
lean_dec(v___x_1214_);
lean_dec_ref(v_self_1213_);
v_a_1198_ = v_snd_1192_;
goto v___jp_1197_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1207_);
lean_del_object(v___x_1194_);
lean_dec(v_snd_1192_);
lean_dec_ref(v___x_1180_);
v_a_1217_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1210_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_del_object(v___x_1194_);
lean_dec(v_snd_1192_);
lean_dec_ref(v___x_1180_);
v_a_1225_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1206_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1206_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
v___jp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_a_1198_);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1198_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
size_t v___x_1201_; size_t v___x_1202_; 
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1183_, v___x_1201_);
v_i_1183_ = v___x_1202_;
v_b_1184_ = v___x_1200_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1235_, lean_object* v___x_1236_, lean_object* v_as_1237_, lean_object* v_sz_1238_, lean_object* v_i_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1238_);
lean_dec(v_sz_1238_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1235_, v___x_1236_, v_as_1237_, v_sz_boxed_1246_, v_i_boxed_1247_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec_ref(v_as_1237_);
lean_dec_ref(v_goal_1235_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1249_, lean_object* v___x_1250_, lean_object* v_as_1251_, size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v___x_1250_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_b_1254_);
return v___x_1261_;
}
else
{
lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1303_; 
v_snd_1262_ = lean_ctor_get(v_b_1254_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_b_1254_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v_b_1254_, 0);
lean_dec(v_unused_1304_);
v___x_1264_ = v_b_1254_;
v_isShared_1265_ = v_isSharedCheck_1303_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_dec(v_b_1254_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1303_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v_a_1268_; lean_object* v_a_1275_; lean_object* v___x_1276_; 
v___x_1266_ = lean_box(0);
v_a_1275_ = lean_array_uget_borrowed(v_as_1251_, v_i_1253_);
lean_inc(v_a_1275_);
v___x_1276_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1249_, v_a_1275_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; uint8_t v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1277_);
if (v___x_1278_ == 0)
{
lean_dec(v_a_1277_);
v_a_1268_ = v_snd_1262_;
goto v___jp_1267_;
}
else
{
lean_object* v_type_1279_; lean_object* v___x_1280_; 
v_type_1279_ = lean_ctor_get(v___x_1250_, 2);
lean_inc(v_a_1277_);
lean_inc_ref(v_type_1279_);
v___x_1280_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1279_, v_a_1277_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; uint8_t v___x_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_unbox(v_a_1281_);
lean_dec(v_a_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v_a_1277_);
v_a_1268_ = v_snd_1262_;
goto v___jp_1267_;
}
else
{
lean_object* v_self_1283_; lean_object* v___x_1284_; 
v_self_1283_ = lean_ctor_get(v_a_1277_, 0);
lean_inc_ref(v_self_1283_);
lean_dec(v_a_1277_);
v___x_1284_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1250_, v_self_1283_);
if (lean_obj_tag(v___x_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1249_, v_self_1283_, v_val_1285_, v_snd_1262_);
v_a_1268_ = v___x_1286_;
goto v___jp_1267_;
}
else
{
lean_dec(v___x_1284_);
lean_dec_ref(v_self_1283_);
v_a_1268_ = v_snd_1262_;
goto v___jp_1267_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1277_);
lean_del_object(v___x_1264_);
lean_dec(v_snd_1262_);
lean_dec_ref(v___x_1250_);
v_a_1287_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1280_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1280_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_del_object(v___x_1264_);
lean_dec(v_snd_1262_);
lean_dec_ref(v___x_1250_);
v_a_1295_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1276_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1276_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
v___jp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_a_1268_);
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1270_ = v___x_1264_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_a_1268_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1253_, v___x_1271_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1249_, v___x_1250_, v_as_1251_, v_sz_1252_, v___x_1272_, v___x_1270_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1305_, lean_object* v___x_1306_, lean_object* v_as_1307_, lean_object* v_sz_1308_, lean_object* v_i_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
size_t v_sz_boxed_1316_; size_t v_i_boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1308_);
lean_dec(v_sz_1308_);
v_i_boxed_1317_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1305_, v___x_1306_, v_as_1307_, v_sz_boxed_1316_, v_i_boxed_1317_, v_b_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_as_1307_);
lean_dec_ref(v_goal_1305_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1319_, lean_object* v_goal_1320_, lean_object* v___x_1321_, lean_object* v_n_1322_, lean_object* v_b_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
if (lean_obj_tag(v_n_1322_) == 0)
{
lean_object* v_cs_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; size_t v_sz_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v_cs_1329_ = lean_ctor_get(v_n_1322_, 0);
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_b_1323_);
v_sz_1332_ = lean_array_size(v_cs_1329_);
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1319_, v_goal_1320_, v___x_1321_, v_cs_1329_, v_sz_1332_, v___x_1333_, v___x_1331_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1349_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1349_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1349_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_fst_1339_; 
v_fst_1339_ = lean_ctor_get(v_a_1335_, 0);
if (lean_obj_tag(v_fst_1339_) == 0)
{
lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_snd_1340_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_snd_1340_);
lean_dec(v_a_1335_);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_snd_1340_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1341_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
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
lean_object* v_val_1345_; lean_object* v___x_1347_; 
lean_inc_ref(v_fst_1339_);
lean_dec(v_a_1335_);
v_val_1345_ = lean_ctor_get(v_fst_1339_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v_fst_1339_, 1);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_val_1345_);
v___x_1347_ = v___x_1337_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_val_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1334_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1334_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_vs_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v_vs_1358_ = lean_ctor_get(v_n_1322_, 0);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_b_1323_);
v_sz_1361_ = lean_array_size(v_vs_1358_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1320_, v___x_1321_, v_vs_1358_, v_sz_1361_, v___x_1362_, v___x_1360_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1378_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1378_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_fst_1368_; 
v_fst_1368_ = lean_ctor_get(v_a_1364_, 0);
if (lean_obj_tag(v_fst_1368_) == 0)
{
lean_object* v_snd_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v_snd_1369_ = lean_ctor_get(v_a_1364_, 1);
lean_inc(v_snd_1369_);
lean_dec(v_a_1364_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_snd_1369_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_val_1374_; lean_object* v___x_1376_; 
lean_inc_ref(v_fst_1368_);
lean_dec(v_a_1364_);
v_val_1374_ = lean_ctor_get(v_fst_1368_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v_fst_1368_, 1);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_val_1374_);
v___x_1376_ = v___x_1366_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_val_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1363_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1363_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1387_, lean_object* v_goal_1388_, lean_object* v___x_1389_, lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v___x_1389_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_b_1393_);
return v___x_1400_;
}
else
{
lean_object* v_snd_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1435_; 
v_snd_1401_ = lean_ctor_get(v_b_1393_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_b_1393_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_b_1393_, 0);
lean_dec(v_unused_1436_);
v___x_1403_ = v_b_1393_;
v_isShared_1404_ = v_isSharedCheck_1435_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1401_);
lean_dec(v_b_1393_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1435_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_box(0);
v_a_1406_ = lean_array_uget_borrowed(v_as_1390_, v_i_1392_);
lean_inc(v_snd_1401_);
lean_inc_ref(v___x_1389_);
v___x_1407_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1387_, v_goal_1388_, v___x_1389_, v_a_1406_, v_snd_1401_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1426_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1426_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1426_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
if (lean_obj_tag(v_a_1408_) == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec_ref(v___x_1389_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_a_1408_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1412_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_snd_1401_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1414_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; 
lean_del_object(v___x_1410_);
lean_dec(v_snd_1401_);
v_a_1419_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v_a_1408_, 1);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v_a_1419_);
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1421_ = v___x_1403_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_a_1419_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
size_t v___x_1422_; size_t v___x_1423_; 
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1392_, v___x_1422_);
v_i_1392_ = v___x_1423_;
v_b_1393_ = v___x_1421_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_del_object(v___x_1403_);
lean_dec(v_snd_1401_);
lean_dec_ref(v___x_1389_);
v_a_1427_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1407_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1407_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1437_, lean_object* v_goal_1438_, lean_object* v___x_1439_, lean_object* v_as_1440_, lean_object* v_sz_1441_, lean_object* v_i_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
size_t v_sz_boxed_1449_; size_t v_i_boxed_1450_; lean_object* v_res_1451_; 
v_sz_boxed_1449_ = lean_unbox_usize(v_sz_1441_);
lean_dec(v_sz_1441_);
v_i_boxed_1450_ = lean_unbox_usize(v_i_1442_);
lean_dec(v_i_1442_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1437_, v_goal_1438_, v___x_1439_, v_as_1440_, v_sz_boxed_1449_, v_i_boxed_1450_, v_b_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec_ref(v_as_1440_);
lean_dec_ref(v_goal_1438_);
lean_dec_ref(v_init_1437_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1452_, lean_object* v_goal_1453_, lean_object* v___x_1454_, lean_object* v_n_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1452_, v_goal_1453_, v___x_1454_, v_n_1455_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v_n_1455_);
lean_dec_ref(v_goal_1453_);
lean_dec_ref(v_init_1452_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1463_, lean_object* v___x_1464_, lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___x_1464_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_b_1468_);
return v___x_1475_;
}
else
{
lean_object* v_snd_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1517_; 
v_snd_1476_ = lean_ctor_get(v_b_1468_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_b_1468_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_b_1468_, 0);
lean_dec(v_unused_1518_);
v___x_1478_ = v_b_1468_;
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1476_);
lean_dec(v_b_1468_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1517_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v_a_1482_; lean_object* v_a_1489_; lean_object* v___x_1490_; 
v___x_1480_ = lean_box(0);
v_a_1489_ = lean_array_uget_borrowed(v_as_1465_, v_i_1467_);
lean_inc(v_a_1489_);
v___x_1490_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1463_, v_a_1489_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; uint8_t v___x_1492_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v_a_1491_);
v_a_1482_ = v_snd_1476_;
goto v___jp_1481_;
}
else
{
lean_object* v_type_1493_; lean_object* v___x_1494_; 
v_type_1493_ = lean_ctor_get(v___x_1464_, 2);
lean_inc(v_a_1491_);
lean_inc_ref(v_type_1493_);
v___x_1494_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1493_, v_a_1491_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; uint8_t v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = lean_unbox(v_a_1495_);
lean_dec(v_a_1495_);
if (v___x_1496_ == 0)
{
lean_dec(v_a_1491_);
v_a_1482_ = v_snd_1476_;
goto v___jp_1481_;
}
else
{
lean_object* v_self_1497_; lean_object* v___x_1498_; 
v_self_1497_ = lean_ctor_get(v_a_1491_, 0);
lean_inc_ref(v_self_1497_);
lean_dec(v_a_1491_);
v___x_1498_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1464_, v_self_1497_);
if (lean_obj_tag(v___x_1498_) == 1)
{
lean_object* v_val_1499_; lean_object* v___x_1500_; 
v_val_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1463_, v_self_1497_, v_val_1499_, v_snd_1476_);
v_a_1482_ = v___x_1500_;
goto v___jp_1481_;
}
else
{
lean_dec(v___x_1498_);
lean_dec_ref(v_self_1497_);
v_a_1482_ = v_snd_1476_;
goto v___jp_1481_;
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1491_);
lean_del_object(v___x_1478_);
lean_dec(v_snd_1476_);
lean_dec_ref(v___x_1464_);
v_a_1501_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1494_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1494_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_del_object(v___x_1478_);
lean_dec(v_snd_1476_);
lean_dec_ref(v___x_1464_);
v_a_1509_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1490_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1490_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
v___jp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v_a_1482_);
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1484_ = v___x_1478_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_a_1482_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
size_t v___x_1485_; size_t v___x_1486_; 
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1467_, v___x_1485_);
v_i_1467_ = v___x_1486_;
v_b_1468_ = v___x_1484_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1519_, lean_object* v___x_1520_, lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1519_, v___x_1520_, v_as_1521_, v_sz_boxed_1530_, v_i_boxed_1531_, v_b_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_as_1521_);
lean_dec_ref(v_goal_1519_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1533_, lean_object* v___x_1534_, lean_object* v_as_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v___x_1534_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_b_1538_);
return v___x_1545_;
}
else
{
lean_object* v_snd_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1587_; 
v_snd_1546_ = lean_ctor_get(v_b_1538_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_b_1538_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v_b_1538_, 0);
lean_dec(v_unused_1588_);
v___x_1548_ = v_b_1538_;
v_isShared_1549_ = v_isSharedCheck_1587_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_snd_1546_);
lean_dec(v_b_1538_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1587_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v_a_1552_; lean_object* v_a_1559_; lean_object* v___x_1560_; 
v___x_1550_ = lean_box(0);
v_a_1559_ = lean_array_uget_borrowed(v_as_1535_, v_i_1537_);
lean_inc(v_a_1559_);
v___x_1560_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1533_, v_a_1559_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1561_);
if (v___x_1562_ == 0)
{
lean_dec(v_a_1561_);
v_a_1552_ = v_snd_1546_;
goto v___jp_1551_;
}
else
{
lean_object* v_type_1563_; lean_object* v___x_1564_; 
v_type_1563_ = lean_ctor_get(v___x_1534_, 2);
lean_inc(v_a_1561_);
lean_inc_ref(v_type_1563_);
v___x_1564_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1563_, v_a_1561_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; uint8_t v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_unbox(v_a_1565_);
lean_dec(v_a_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v_a_1561_);
v_a_1552_ = v_snd_1546_;
goto v___jp_1551_;
}
else
{
lean_object* v_self_1567_; lean_object* v___x_1568_; 
v_self_1567_ = lean_ctor_get(v_a_1561_, 0);
lean_inc_ref(v_self_1567_);
lean_dec(v_a_1561_);
v___x_1568_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1534_, v_self_1567_);
if (lean_obj_tag(v___x_1568_) == 1)
{
lean_object* v_val_1569_; lean_object* v___x_1570_; 
v_val_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1533_, v_self_1567_, v_val_1569_, v_snd_1546_);
v_a_1552_ = v___x_1570_;
goto v___jp_1551_;
}
else
{
lean_dec(v___x_1568_);
lean_dec_ref(v_self_1567_);
v_a_1552_ = v_snd_1546_;
goto v___jp_1551_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1561_);
lean_del_object(v___x_1548_);
lean_dec(v_snd_1546_);
lean_dec_ref(v___x_1534_);
v_a_1571_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1564_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1564_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1548_);
lean_dec(v_snd_1546_);
lean_dec_ref(v___x_1534_);
v_a_1579_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1560_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1560_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
v___jp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v_a_1552_);
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1554_ = v___x_1548_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_a_1552_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_add(v_i_1537_, v___x_1555_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1533_, v___x_1534_, v_as_1535_, v_sz_1536_, v___x_1556_, v___x_1554_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1589_, lean_object* v___x_1590_, lean_object* v_as_1591_, lean_object* v_sz_1592_, lean_object* v_i_1593_, lean_object* v_b_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
size_t v_sz_boxed_1600_; size_t v_i_boxed_1601_; lean_object* v_res_1602_; 
v_sz_boxed_1600_ = lean_unbox_usize(v_sz_1592_);
lean_dec(v_sz_1592_);
v_i_boxed_1601_ = lean_unbox_usize(v_i_1593_);
lean_dec(v_i_1593_);
v_res_1602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1589_, v___x_1590_, v_as_1591_, v_sz_boxed_1600_, v_i_boxed_1601_, v_b_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_as_1591_);
lean_dec_ref(v_goal_1589_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1603_, lean_object* v___x_1604_, lean_object* v_t_1605_, lean_object* v_init_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_root_1612_; lean_object* v_tail_1613_; lean_object* v___x_1614_; 
v_root_1612_ = lean_ctor_get(v_t_1605_, 0);
v_tail_1613_ = lean_ctor_get(v_t_1605_, 1);
lean_inc_ref(v___x_1604_);
lean_inc_ref(v_init_1606_);
v___x_1614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1606_, v_goal_1603_, v___x_1604_, v_root_1612_, v_init_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec_ref(v_init_1606_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1651_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1651_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1651_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
if (lean_obj_tag(v_a_1615_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v___x_1604_);
v_a_1619_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v_a_1615_, 1);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_a_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; size_t v_sz_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
lean_del_object(v___x_1617_);
v_a_1623_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v_a_1615_, 1);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_a_1623_);
v_sz_1626_ = lean_array_size(v_tail_1613_);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1603_, v___x_1604_, v_tail_1613_, v_sz_1626_, v___x_1627_, v___x_1625_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1642_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_fst_1633_; 
v_fst_1633_ = lean_ctor_get(v_a_1629_, 0);
if (lean_obj_tag(v_fst_1633_) == 0)
{
lean_object* v_snd_1634_; lean_object* v___x_1636_; 
v_snd_1634_ = lean_ctor_get(v_a_1629_, 1);
lean_inc(v_snd_1634_);
lean_dec(v_a_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_snd_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_snd_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
else
{
lean_object* v_val_1638_; lean_object* v___x_1640_; 
lean_inc_ref(v_fst_1633_);
lean_dec(v_a_1629_);
v_val_1638_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v_fst_1633_, 1);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_val_1638_);
v___x_1640_ = v___x_1631_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_val_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1628_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1628_);
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
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1604_);
v_a_1652_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1614_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1614_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1660_, lean_object* v___x_1661_, lean_object* v_t_1662_, lean_object* v_init_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1660_, v___x_1661_, v_t_1662_, v_init_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v_t_1662_);
lean_dec_ref(v_goal_1660_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1670_, lean_object* v_as_1671_, size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_b_1674_);
return v___x_1681_;
}
else
{
lean_object* v_snd_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1713_; 
v_snd_1682_ = lean_ctor_get(v_b_1674_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_b_1674_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v_b_1674_, 0);
lean_dec(v_unused_1714_);
v___x_1684_ = v_b_1674_;
v_isShared_1685_ = v_isSharedCheck_1713_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_snd_1682_);
lean_dec(v_b_1674_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1713_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v_a_1688_; lean_object* v_a_1695_; lean_object* v___x_1696_; 
v___x_1686_ = lean_box(0);
v_a_1695_ = lean_array_uget_borrowed(v_as_1671_, v_i_1673_);
lean_inc(v_a_1695_);
v___x_1696_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1670_, v_a_1695_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v_self_1698_; lean_object* v___x_1699_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v_self_1698_ = lean_ctor_get(v_a_1697_, 0);
lean_inc_ref(v_self_1698_);
lean_dec(v_a_1697_);
v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1698_);
if (lean_obj_tag(v___x_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1701_; 
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1682_, v_val_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1682_, v_self_1698_);
lean_dec_ref(v_self_1698_);
if (lean_obj_tag(v___x_1702_) == 1)
{
lean_object* v_val_1703_; lean_object* v___x_1704_; 
v_val_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1670_, v_val_1700_, v_val_1703_, v_snd_1682_);
v_a_1688_ = v___x_1704_;
goto v___jp_1687_;
}
else
{
lean_dec(v___x_1702_);
lean_dec(v_val_1700_);
v_a_1688_ = v_snd_1682_;
goto v___jp_1687_;
}
}
else
{
lean_dec_ref_known(v___x_1701_, 1);
lean_dec(v_val_1700_);
lean_dec_ref(v_self_1698_);
v_a_1688_ = v_snd_1682_;
goto v___jp_1687_;
}
}
else
{
lean_dec(v___x_1699_);
lean_dec_ref(v_self_1698_);
v_a_1688_ = v_snd_1682_;
goto v___jp_1687_;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_del_object(v___x_1684_);
lean_dec(v_snd_1682_);
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1696_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1696_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
v___jp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_a_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1690_ = v___x_1684_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_a_1688_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
size_t v___x_1691_; size_t v___x_1692_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1673_, v___x_1691_);
v_i_1673_ = v___x_1692_;
v_b_1674_ = v___x_1690_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1715_, lean_object* v_as_1716_, lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
size_t v_sz_boxed_1725_; size_t v_i_boxed_1726_; lean_object* v_res_1727_; 
v_sz_boxed_1725_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1726_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1715_, v_as_1716_, v_sz_boxed_1725_, v_i_boxed_1726_, v_b_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_as_1716_);
lean_dec_ref(v_goal_1715_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1728_, lean_object* v_as_1729_, size_t v_sz_1730_, size_t v_i_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1731_, v_sz_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1732_);
return v___x_1739_;
}
else
{
lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1771_; 
v_snd_1740_ = lean_ctor_get(v_b_1732_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_b_1732_, 0);
lean_dec(v_unused_1772_);
v___x_1742_ = v_b_1732_;
v_isShared_1743_ = v_isSharedCheck_1771_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_dec(v_b_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1771_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v_a_1746_; lean_object* v_a_1753_; lean_object* v___x_1754_; 
v___x_1744_ = lean_box(0);
v_a_1753_ = lean_array_uget_borrowed(v_as_1729_, v_i_1731_);
lean_inc(v_a_1753_);
v___x_1754_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1728_, v_a_1753_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_self_1756_; lean_object* v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v_self_1756_ = lean_ctor_get(v_a_1755_, 0);
lean_inc_ref(v_self_1756_);
lean_dec(v_a_1755_);
v___x_1757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1756_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1759_; 
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1740_, v_val_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1740_, v_self_1756_);
lean_dec_ref(v_self_1756_);
if (lean_obj_tag(v___x_1760_) == 1)
{
lean_object* v_val_1761_; lean_object* v___x_1762_; 
v_val_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1728_, v_val_1758_, v_val_1761_, v_snd_1740_);
v_a_1746_ = v___x_1762_;
goto v___jp_1745_;
}
else
{
lean_dec(v___x_1760_);
lean_dec(v_val_1758_);
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
}
else
{
lean_dec_ref_known(v___x_1759_, 1);
lean_dec(v_val_1758_);
lean_dec_ref(v_self_1756_);
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
}
else
{
lean_dec(v___x_1757_);
lean_dec_ref(v_self_1756_);
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_del_object(v___x_1742_);
lean_dec(v_snd_1740_);
v_a_1763_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1754_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1754_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
v___jp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1746_);
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1746_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1731_, v___x_1749_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1728_, v_as_1729_, v_sz_1730_, v___x_1750_, v___x_1748_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1773_, lean_object* v_as_1774_, lean_object* v_sz_1775_, lean_object* v_i_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1775_);
lean_dec(v_sz_1775_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1773_, v_as_1774_, v_sz_boxed_1783_, v_i_boxed_1784_, v_b_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_as_1774_);
lean_dec_ref(v_goal_1773_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1786_, lean_object* v_as_1787_, size_t v_sz_1788_, size_t v_i_1789_, lean_object* v_b_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_lt(v_i_1789_, v_sz_1788_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_b_1790_);
return v___x_1797_;
}
else
{
lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1829_; 
v_snd_1798_ = lean_ctor_get(v_b_1790_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_b_1790_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_b_1790_, 0);
lean_dec(v_unused_1830_);
v___x_1800_ = v_b_1790_;
v_isShared_1801_ = v_isSharedCheck_1829_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_dec(v_b_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1829_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v_a_1804_; lean_object* v_a_1811_; lean_object* v___x_1812_; 
v___x_1802_ = lean_box(0);
v_a_1811_ = lean_array_uget_borrowed(v_as_1787_, v_i_1789_);
lean_inc(v_a_1811_);
v___x_1812_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1786_, v_a_1811_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v_self_1814_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v_self_1814_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_ref(v_self_1814_);
lean_dec(v_a_1813_);
v___x_1815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1814_);
if (lean_obj_tag(v___x_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; 
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v___x_1817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1798_, v_val_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1798_, v_self_1814_);
lean_dec_ref(v_self_1814_);
if (lean_obj_tag(v___x_1818_) == 1)
{
lean_object* v_val_1819_; lean_object* v___x_1820_; 
v_val_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1786_, v_val_1816_, v_val_1819_, v_snd_1798_);
v_a_1804_ = v___x_1820_;
goto v___jp_1803_;
}
else
{
lean_dec(v___x_1818_);
lean_dec(v_val_1816_);
v_a_1804_ = v_snd_1798_;
goto v___jp_1803_;
}
}
else
{
lean_dec_ref_known(v___x_1817_, 1);
lean_dec(v_val_1816_);
lean_dec_ref(v_self_1814_);
v_a_1804_ = v_snd_1798_;
goto v___jp_1803_;
}
}
else
{
lean_dec(v___x_1815_);
lean_dec_ref(v_self_1814_);
v_a_1804_ = v_snd_1798_;
goto v___jp_1803_;
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_del_object(v___x_1800_);
lean_dec(v_snd_1798_);
v_a_1821_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1812_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1812_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v_a_1804_);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1806_ = v___x_1800_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_a_1804_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
size_t v___x_1807_; size_t v___x_1808_; 
v___x_1807_ = ((size_t)1ULL);
v___x_1808_ = lean_usize_add(v_i_1789_, v___x_1807_);
v_i_1789_ = v___x_1808_;
v_b_1790_ = v___x_1806_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1831_, lean_object* v_as_1832_, lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
size_t v_sz_boxed_1841_; size_t v_i_boxed_1842_; lean_object* v_res_1843_; 
v_sz_boxed_1841_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1842_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1831_, v_as_1832_, v_sz_boxed_1841_, v_i_boxed_1842_, v_b_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v_as_1832_);
lean_dec_ref(v_goal_1831_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1844_, lean_object* v_as_1845_, size_t v_sz_1846_, size_t v_i_1847_, lean_object* v_b_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_usize_dec_lt(v_i_1847_, v_sz_1846_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_b_1848_);
return v___x_1855_;
}
else
{
lean_object* v_snd_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1887_; 
v_snd_1856_ = lean_ctor_get(v_b_1848_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_b_1848_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_b_1848_, 0);
lean_dec(v_unused_1888_);
v___x_1858_ = v_b_1848_;
v_isShared_1859_ = v_isSharedCheck_1887_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snd_1856_);
lean_dec(v_b_1848_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1887_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v_a_1862_; lean_object* v_a_1869_; lean_object* v___x_1870_; 
v___x_1860_ = lean_box(0);
v_a_1869_ = lean_array_uget_borrowed(v_as_1845_, v_i_1847_);
lean_inc(v_a_1869_);
v___x_1870_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1844_, v_a_1869_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v_self_1872_; lean_object* v___x_1873_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v_self_1872_ = lean_ctor_get(v_a_1871_, 0);
lean_inc_ref(v_self_1872_);
lean_dec(v_a_1871_);
v___x_1873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1872_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v___x_1875_; 
v_val_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1856_, v_val_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1856_, v_self_1872_);
lean_dec_ref(v_self_1872_);
if (lean_obj_tag(v___x_1876_) == 1)
{
lean_object* v_val_1877_; lean_object* v___x_1878_; 
v_val_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1844_, v_val_1874_, v_val_1877_, v_snd_1856_);
v_a_1862_ = v___x_1878_;
goto v___jp_1861_;
}
else
{
lean_dec(v___x_1876_);
lean_dec(v_val_1874_);
v_a_1862_ = v_snd_1856_;
goto v___jp_1861_;
}
}
else
{
lean_dec_ref_known(v___x_1875_, 1);
lean_dec(v_val_1874_);
lean_dec_ref(v_self_1872_);
v_a_1862_ = v_snd_1856_;
goto v___jp_1861_;
}
}
else
{
lean_dec(v___x_1873_);
lean_dec_ref(v_self_1872_);
v_a_1862_ = v_snd_1856_;
goto v___jp_1861_;
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_del_object(v___x_1858_);
lean_dec(v_snd_1856_);
v_a_1879_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1870_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1870_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
v___jp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_a_1862_);
lean_ctor_set(v___x_1858_, 0, v___x_1860_);
v___x_1864_ = v___x_1858_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_a_1862_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1847_, v___x_1865_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1844_, v_as_1845_, v_sz_1846_, v___x_1866_, v___x_1864_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1889_, lean_object* v_as_1890_, lean_object* v_sz_1891_, lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
size_t v_sz_boxed_1899_; size_t v_i_boxed_1900_; lean_object* v_res_1901_; 
v_sz_boxed_1899_ = lean_unbox_usize(v_sz_1891_);
lean_dec(v_sz_1891_);
v_i_boxed_1900_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1889_, v_as_1890_, v_sz_boxed_1899_, v_i_boxed_1900_, v_b_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_as_1890_);
lean_dec_ref(v_goal_1889_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1902_, lean_object* v_goal_1903_, lean_object* v_n_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
if (lean_obj_tag(v_n_1904_) == 0)
{
lean_object* v_cs_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v_cs_1911_ = lean_ctor_get(v_n_1904_, 0);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v_b_1905_);
v_sz_1914_ = lean_array_size(v_cs_1911_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1902_, v_goal_1903_, v_cs_1911_, v_sz_1914_, v___x_1915_, v___x_1913_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1931_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_fst_1921_; 
v_fst_1921_ = lean_ctor_get(v_a_1917_, 0);
if (lean_obj_tag(v_fst_1921_) == 0)
{
lean_object* v_snd_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v_snd_1922_ = lean_ctor_get(v_a_1917_, 1);
lean_inc(v_snd_1922_);
lean_dec(v_a_1917_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_snd_1922_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1923_);
v___x_1925_ = v___x_1919_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
lean_object* v_val_1927_; lean_object* v___x_1929_; 
lean_inc_ref(v_fst_1921_);
lean_dec(v_a_1917_);
v_val_1927_ = lean_ctor_get(v_fst_1921_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v_fst_1921_, 1);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_val_1927_);
v___x_1929_ = v___x_1919_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_val_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1916_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1916_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_vs_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; size_t v_sz_1943_; size_t v___x_1944_; lean_object* v___x_1945_; 
v_vs_1940_ = lean_ctor_get(v_n_1904_, 0);
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_b_1905_);
v_sz_1943_ = lean_array_size(v_vs_1940_);
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1903_, v_vs_1940_, v_sz_1943_, v___x_1944_, v___x_1942_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1960_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1960_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1960_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_fst_1950_; 
v_fst_1950_ = lean_ctor_get(v_a_1946_, 0);
if (lean_obj_tag(v_fst_1950_) == 0)
{
lean_object* v_snd_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_snd_1951_ = lean_ctor_get(v_a_1946_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_a_1946_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_snd_1951_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1952_);
v___x_1954_ = v___x_1948_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
else
{
lean_object* v_val_1956_; lean_object* v___x_1958_; 
lean_inc_ref(v_fst_1950_);
lean_dec(v_a_1946_);
v_val_1956_ = lean_ctor_get(v_fst_1950_, 0);
lean_inc(v_val_1956_);
lean_dec_ref_known(v_fst_1950_, 1);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v_val_1956_);
v___x_1958_ = v___x_1948_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_val_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1945_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1945_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1969_, lean_object* v_goal_1970_, lean_object* v_as_1971_, size_t v_sz_1972_, size_t v_i_1973_, lean_object* v_b_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_lt(v_i_1973_, v_sz_1972_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_b_1974_);
return v___x_1981_;
}
else
{
lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2016_; 
v_snd_1982_ = lean_ctor_get(v_b_1974_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_b_1974_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v_b_1974_, 0);
lean_dec(v_unused_2017_);
v___x_1984_ = v_b_1974_;
v_isShared_1985_ = v_isSharedCheck_2016_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_dec(v_b_1974_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2016_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v_a_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v_a_1987_ = lean_array_uget_borrowed(v_as_1971_, v_i_1973_);
lean_inc(v_snd_1982_);
v___x_1988_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1969_, v_goal_1970_, v_a_1987_, v_snd_1982_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2007_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2007_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2007_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
if (lean_obj_tag(v_a_1989_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_a_1989_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1993_);
v___x_1995_ = v___x_1984_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1982_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1995_);
v___x_1997_ = v___x_1991_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; 
lean_del_object(v___x_1991_);
lean_dec(v_snd_1982_);
v_a_2000_ = lean_ctor_get(v_a_1989_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v_a_1989_, 1);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v_a_2000_);
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_2002_ = v___x_1984_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_2000_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
size_t v___x_2003_; size_t v___x_2004_; 
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1973_, v___x_2003_);
v_i_1973_ = v___x_2004_;
v_b_1974_ = v___x_2002_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_del_object(v___x_1984_);
lean_dec(v_snd_1982_);
v_a_2008_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1988_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1988_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2018_, lean_object* v_goal_2019_, lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2018_, v_goal_2019_, v_as_2020_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_as_2020_);
lean_dec_ref(v_goal_2019_);
lean_dec_ref(v_init_2018_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2032_, lean_object* v_goal_2033_, lean_object* v_n_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2032_, v_goal_2033_, v_n_2034_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_n_2034_);
lean_dec_ref(v_goal_2033_);
lean_dec_ref(v_init_2032_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2042_, lean_object* v_t_2043_, lean_object* v_init_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_root_2050_; lean_object* v_tail_2051_; lean_object* v___x_2052_; 
v_root_2050_ = lean_ctor_get(v_t_2043_, 0);
v_tail_2051_ = lean_ctor_get(v_t_2043_, 1);
lean_inc_ref(v_init_2044_);
v___x_2052_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2044_, v_goal_2042_, v_root_2050_, v_init_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec_ref(v_init_2044_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2089_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2089_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2089_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
if (lean_obj_tag(v_a_2053_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; 
v_a_2057_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v_a_2053_, 1);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_a_2057_);
v___x_2059_ = v___x_2055_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
lean_del_object(v___x_2055_);
v_a_2061_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v_a_2053_, 1);
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_a_2061_);
v_sz_2064_ = lean_array_size(v_tail_2051_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2042_, v_tail_2051_, v_sz_2064_, v___x_2065_, v___x_2063_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2080_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; 
v_fst_2071_ = lean_ctor_get(v_a_2067_, 0);
if (lean_obj_tag(v_fst_2071_) == 0)
{
lean_object* v_snd_2072_; lean_object* v___x_2074_; 
v_snd_2072_ = lean_ctor_get(v_a_2067_, 1);
lean_inc(v_snd_2072_);
lean_dec(v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v_snd_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_snd_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; 
lean_inc_ref(v_fst_2071_);
lean_dec(v_a_2067_);
v_val_2076_ = lean_ctor_get(v_fst_2071_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v_fst_2071_, 1);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v_val_2076_);
v___x_2078_ = v___x_2069_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_val_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2066_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2066_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2052_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2052_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2098_, lean_object* v_t_2099_, lean_object* v_init_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2098_, v_t_2099_, v_init_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_t_2099_);
lean_dec_ref(v_goal_2098_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_unsigned_to_nat(16u);
v___x_2109_ = lean_mk_array(v___x_2108_, v___x_2107_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_model_2112_; 
v___x_2110_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2111_ = lean_unsigned_to_nat(0u);
v_model_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2112_, 0, v___x_2111_);
lean_ctor_set(v_model_2112_, 1, v___x_2110_);
return v_model_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2120_, lean_object* v_structId_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_ref_2127_; lean_object* v___x_2128_; lean_object* v_model_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_ref_2127_ = lean_ctor_get(v_a_2124_, 2);
v___x_2128_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2129_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2130_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2131_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2130_, v_goal_2120_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v_toGoalState_2133_; lean_object* v_structs_2134_; lean_object* v_exprs_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v_toGoalState_2133_ = lean_ctor_get(v_goal_2120_, 0);
v_structs_2134_ = lean_ctor_get(v_a_2132_, 0);
lean_inc_ref(v_structs_2134_);
lean_dec(v_a_2132_);
v_exprs_2135_ = lean_ctor_get(v_toGoalState_2133_, 2);
v___x_2136_ = lean_array_get(v___x_2128_, v_structs_2134_, v_structId_2121_);
lean_dec_ref(v_structs_2134_);
lean_inc(v___x_2136_);
v___x_2137_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2120_, v___x_2136_, v_exprs_2135_, v_model_2129_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2120_, v_structId_2121_, v_a_2138_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2120_, v_exprs_2135_, v_a_2140_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_type_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v_type_2143_ = lean_ctor_get(v___x_2136_, 2);
lean_inc_ref(v_type_2143_);
lean_dec(v___x_2136_);
v___x_2144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2144_, 0, v_type_2143_);
v___x_2145_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2120_, v___x_2144_, v_a_2142_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2148_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2147_, v_a_2146_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2156_);
v___x_2150_ = v___x_2148_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v___x_2148_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v_a_2146_);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2146_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_2146_);
v_a_2157_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2148_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2148_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
return v___x_2145_;
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v___x_2136_);
v_a_2165_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2141_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2141_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v___x_2136_);
v_a_2173_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2139_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2139_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v___x_2136_);
v_a_2181_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2137_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2137_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2200_; 
v_a_2189_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2191_ = v___x_2131_;
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2131_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2193_ = lean_io_error_to_string(v_a_2189_);
v___x_2194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
v___x_2195_ = l_Lean_MessageData_ofFormat(v___x_2194_);
lean_inc(v_ref_2127_);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_ref_2127_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2196_);
v___x_2198_ = v___x_2191_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2201_, lean_object* v_structId_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2201_, v_structId_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_structId_2202_);
lean_dec_ref(v_goal_2201_);
return v_res_2208_;
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

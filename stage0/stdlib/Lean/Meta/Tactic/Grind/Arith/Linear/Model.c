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
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(lean_object* v_x_22_, size_t v_x_23_, lean_object* v_x_24_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_22_ = stack[0].m_obj;
size_t v_x_23_ = stack[1].m_num;
lean_object* v_x_24_ = stack[2].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_22_, v_x_23_, v_x_24_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
size_t v_x_370__boxed_51_; lean_object* v_res_52_; 
v_x_370__boxed_51_ = lean_unbox_usize(v_x_49_);
lean_dec(v_x_49_);
v_res_52_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_48_, v_x_370__boxed_51_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_48_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; uint64_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_55_ = lean_ptr_addr(v_x_54_);
v___x_56_ = ((size_t)3ULL);
v___x_57_ = lean_usize_shift_right(v___x_55_, v___x_56_);
v___x_58_ = lean_usize_to_uint64(v___x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_53_, v___x_59_, v_x_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_61_, v_x_62_);
lean_dec_ref(v_x_62_);
lean_dec_ref(v_x_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object* v_s_64_, lean_object* v_e_65_){
_start:
{
lean_object* v_varMap_66_; lean_object* v_assignment_67_; lean_object* v___x_68_; 
v_varMap_66_ = lean_ctor_get(v_s_64_, 31);
v_assignment_67_ = lean_ctor_get(v_s_64_, 35);
v___x_68_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_66_, v_e_65_);
if (lean_obj_tag(v___x_68_) == 1)
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_81_; 
v_val_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_81_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_81_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_81_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_size_73_; uint8_t v___x_74_; 
v_size_73_ = lean_ctor_get(v_assignment_67_, 2);
v___x_74_ = lean_nat_dec_lt(v_val_69_, v_size_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_del_object(v___x_71_);
lean_dec(v_val_69_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = l_instInhabitedRat;
v___x_77_ = l_Lean_PersistentArray_get_x21___redArg(v___x_76_, v_assignment_67_, v_val_69_);
lean_dec(v_val_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_77_);
v___x_79_ = v___x_71_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v___x_82_; 
lean_dec(v___x_68_);
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object* v_s_83_, lean_object* v_e_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_83_, v_e_84_);
lean_dec_ref(v_e_84_);
lean_dec_ref(v_s_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object* v_00_u03b2_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_87_, v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object* v_00_u03b2_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_90_, v_x_91_, v_x_92_);
lean_dec_ref(v_x_92_);
lean_dec_ref(v_x_91_);
return v_res_93_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object* v_00_u03b2_94_, lean_object* v_x_95_, size_t v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_95_, v_x_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_95_ = stack[1].m_obj;
size_t v_x_96_ = stack[2].m_num;
lean_object* v_x_97_ = stack[3].m_obj;
lean_object* v_res_99_;
v_res_99_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_box(0), v_x_95_, v_x_96_, v_x_97_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_100_, lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
size_t v_x_531__boxed_104_; lean_object* v_res_105_; 
v_x_531__boxed_104_ = lean_unbox_usize(v_x_102_);
lean_dec(v_x_102_);
v_res_105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_100_, v_x_101_, v_x_531__boxed_104_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_106_, lean_object* v_keys_107_, lean_object* v_vals_108_, lean_object* v_heq_109_, lean_object* v_i_110_, lean_object* v_k_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_107_, v_vals_108_, v_i_110_, v_k_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_113_, lean_object* v_keys_114_, lean_object* v_vals_115_, lean_object* v_heq_116_, lean_object* v_i_117_, lean_object* v_k_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_113_, v_keys_114_, v_vals_115_, v_heq_116_, v_i_117_, v_k_118_);
lean_dec_ref(v_k_118_);
lean_dec_ref(v_vals_115_);
lean_dec_ref(v_keys_114_);
return v_res_119_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(lean_object* v_self_120_, lean_object* v_type_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
v___x_127_ = lean_infer_type(v_self_120_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_129_ = l_Lean_Meta_isExprDefEq(v_a_128_, v_type_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec_ref(v_type_121_);
v_a_130_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_127_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_127_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_120_ = stack[0].m_obj;
lean_object* v_type_121_ = stack[1].m_obj;
lean_object* v___y_122_ = stack[2].m_obj;
lean_object* v___y_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v_res_138_;
v_res_138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_120_, v_type_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0___boxed(lean_object* v_self_139_, lean_object* v_type_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_139_, v_type_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v_res_146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_147_, lean_object* v_n_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___y_155_; lean_object* v_self_172_; lean_object* v___x_173_; uint8_t v_transparency_174_; uint8_t v___x_175_; uint8_t v___x_176_; 
v_self_172_ = lean_ctor_get(v_n_148_, 0);
lean_inc_ref(v_self_172_);
lean_dec_ref(v_n_148_);
v___x_173_ = l_Lean_Meta_Context_config(v_a_149_);
v_transparency_174_ = lean_ctor_get_uint8(v___x_173_, 9);
lean_dec_ref(v___x_173_);
v___x_175_ = 1;
v___x_176_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v_keyedConfig_177_; uint8_t v_trackZetaDelta_178_; lean_object* v_zetaDeltaSet_179_; lean_object* v_lctx_180_; lean_object* v_localInstances_181_; lean_object* v_defEqCtx_x3f_182_; lean_object* v_synthPendingDepth_183_; lean_object* v_customCanUnfoldPredicate_x3f_184_; uint8_t v_univApprox_185_; uint8_t v_inTypeClassResolution_186_; uint8_t v_cacheInferType_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_keyedConfig_177_ = lean_ctor_get(v_a_149_, 0);
v_trackZetaDelta_178_ = lean_ctor_get_uint8(v_a_149_, sizeof(void*)*7);
v_zetaDeltaSet_179_ = lean_ctor_get(v_a_149_, 1);
v_lctx_180_ = lean_ctor_get(v_a_149_, 2);
v_localInstances_181_ = lean_ctor_get(v_a_149_, 3);
v_defEqCtx_x3f_182_ = lean_ctor_get(v_a_149_, 4);
v_synthPendingDepth_183_ = lean_ctor_get(v_a_149_, 5);
v_customCanUnfoldPredicate_x3f_184_ = lean_ctor_get(v_a_149_, 6);
v_univApprox_185_ = lean_ctor_get_uint8(v_a_149_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_186_ = lean_ctor_get_uint8(v_a_149_, sizeof(void*)*7 + 2);
v_cacheInferType_187_ = lean_ctor_get_uint8(v_a_149_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_177_);
v___x_188_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_175_, v_keyedConfig_177_);
lean_inc(v_customCanUnfoldPredicate_x3f_184_);
lean_inc(v_synthPendingDepth_183_);
lean_inc(v_defEqCtx_x3f_182_);
lean_inc_ref(v_localInstances_181_);
lean_inc_ref(v_lctx_180_);
lean_inc(v_zetaDeltaSet_179_);
v___x_189_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_zetaDeltaSet_179_);
lean_ctor_set(v___x_189_, 2, v_lctx_180_);
lean_ctor_set(v___x_189_, 3, v_localInstances_181_);
lean_ctor_set(v___x_189_, 4, v_defEqCtx_x3f_182_);
lean_ctor_set(v___x_189_, 5, v_synthPendingDepth_183_);
lean_ctor_set(v___x_189_, 6, v_customCanUnfoldPredicate_x3f_184_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7, v_trackZetaDelta_178_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 1, v_univApprox_185_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 2, v_inTypeClassResolution_186_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 3, v_cacheInferType_187_);
lean_inc(v_a_152_);
lean_inc_ref(v_a_151_);
lean_inc(v_a_150_);
v___x_190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_172_, v_type_147_, v___x_189_, v_a_150_, v_a_151_, v_a_152_);
v___y_155_ = v___x_190_;
goto v___jp_154_;
}
else
{
lean_object* v___x_191_; 
lean_inc(v_a_152_);
lean_inc_ref(v_a_151_);
lean_inc(v_a_150_);
lean_inc_ref(v_a_149_);
v___x_191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___lam__0(v_self_172_, v_type_147_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
v___y_155_ = v___x_191_;
goto v___jp_154_;
}
v___jp_154_:
{
if (lean_obj_tag(v___y_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_156_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___y_155_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___y_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___y_155_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___y_155_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_147_ = stack[0].m_obj;
lean_object* v_n_148_ = stack[1].m_obj;
lean_object* v_a_149_ = stack[2].m_obj;
lean_object* v_a_150_ = stack[3].m_obj;
lean_object* v_a_151_ = stack[4].m_obj;
lean_object* v_a_152_ = stack[5].m_obj;
lean_object* v_res_192_;
v_res_192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_147_, v_n_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_193_, lean_object* v_n_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_193_, v_n_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = l_Lean_Expr_cleanupAnnotations(v_e_212_);
v___x_214_ = l_Lean_Expr_isApp(v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v___x_213_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v_arg_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_arg_216_ = lean_ctor_get(v___x_213_, 1);
lean_inc_ref(v_arg_216_);
v___x_217_ = l_Lean_Expr_appFnCleanup___redArg(v___x_213_);
v___x_218_ = l_Lean_Expr_isApp(v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec_ref(v___x_217_);
lean_dec_ref(v_arg_216_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_217_);
v___x_221_ = l_Lean_Expr_isApp(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v___x_220_);
lean_dec_ref(v_arg_216_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_220_);
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_225_ = l_Lean_Expr_isConstOf(v___x_223_, v___x_224_);
lean_dec_ref(v___x_223_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec_ref(v_arg_216_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_arg_216_);
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Rat_ofInt(v_a_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_nat_to_int(v_a_230_);
v___x_232_ = l_Rat_ofInt(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v_key_236_; lean_object* v_value_237_; lean_object* v_tail_238_; uint8_t v___x_239_; 
v_key_236_ = lean_ctor_get(v_x_234_, 0);
v_value_237_ = lean_ctor_get(v_x_234_, 1);
v_tail_238_ = lean_ctor_get(v_x_234_, 2);
v___x_239_ = lean_expr_eqv(v_key_236_, v_a_233_);
if (v___x_239_ == 0)
{
v_x_234_ = v_tail_238_;
goto _start;
}
else
{
lean_object* v___x_241_; 
lean_inc(v_value_237_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_value_237_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_242_, v_x_243_);
lean_dec(v_x_243_);
lean_dec_ref(v_a_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_buckets_247_; lean_object* v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v_fold_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_buckets_247_ = lean_ctor_get(v_m_245_, 1);
v___x_248_ = lean_array_get_size(v_buckets_247_);
v___x_249_ = l_Lean_Expr_hash(v_a_246_);
v___x_250_ = 32ULL;
v___x_251_ = lean_uint64_shift_right(v___x_249_, v___x_250_);
v_fold_252_ = lean_uint64_xor(v___x_249_, v___x_251_);
v___x_253_ = 16ULL;
v___x_254_ = lean_uint64_shift_right(v_fold_252_, v___x_253_);
v___x_255_ = lean_uint64_xor(v_fold_252_, v___x_254_);
v___x_256_ = lean_uint64_to_usize(v___x_255_);
v___x_257_ = lean_usize_of_nat(v___x_248_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_sub(v___x_257_, v___x_258_);
v___x_260_ = lean_usize_land(v___x_256_, v___x_259_);
v___x_261_ = lean_array_uget_borrowed(v_buckets_247_, v___x_260_);
v___x_262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_246_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_263_, v_a_264_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_m_263_);
return v_res_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_305_, lean_object* v_model_306_, lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_306_, v_e_307_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v___x_317_; 
lean_dec_ref(v_e_307_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_316_);
v___x_318_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_307_, v_a_309_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_581_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_581_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_581_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_581_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = l_Lean_Expr_cleanupAnnotations(v_a_319_);
v___x_324_ = l_Lean_Expr_isApp(v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_323_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v_arg_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_arg_325_ = lean_ctor_get(v___x_323_, 1);
lean_inc_ref(v_arg_325_);
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_323_);
v___x_327_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_327_ == 0)
{
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v_arg_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_arg_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc_ref(v_arg_328_);
v___x_329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = l_Lean_Expr_isApp(v___x_329_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_329_);
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v_arg_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_arg_333_ = lean_ctor_get(v___x_329_, 1);
lean_inc_ref(v_arg_333_);
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_329_);
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_334_, v___x_337_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_339_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_346_ = l_Lean_Expr_isConstOf(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_344_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_344_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_344_, v___x_351_);
lean_dec_ref(v___x_344_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
goto v___jp_313_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_305_, v_arg_333_);
lean_dec_ref(v_arg_333_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
v___x_354_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_354_);
v___x_356_ = v___x_321_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_358_; 
lean_del_object(v___x_321_);
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
if (lean_obj_tag(v_a_359_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_358_;
}
else
{
lean_object* v_val_360_; lean_object* v___x_361_; 
lean_inc_ref(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_val_360_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v_a_359_, 1);
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
if (lean_obj_tag(v_a_362_) == 0)
{
lean_dec(v_val_360_);
return v___x_361_;
}
else
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_378_; 
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_379_);
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_378_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_378_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_val_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_377_; 
v_val_366_ = lean_ctor_get(v_a_362_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_377_ == 0)
{
v___x_368_ = v_a_362_;
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_val_366_);
lean_dec(v_a_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = l_Rat_add(v_val_360_, v_val_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_372_);
v___x_374_ = v___x_364_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
else
{
lean_dec(v_val_360_);
return v___x_361_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_358_;
}
}
}
}
else
{
uint8_t v___x_380_; 
lean_dec_ref(v___x_344_);
v___x_380_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_305_, v_arg_333_);
lean_dec_ref(v_arg_333_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
v___x_381_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_381_);
v___x_383_ = v___x_321_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___x_385_; 
lean_del_object(v___x_321_);
v___x_385_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
if (lean_obj_tag(v_a_386_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_385_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
lean_inc_ref(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v_val_387_ = lean_ctor_get(v_a_386_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_a_386_, 1);
v___x_388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
if (lean_obj_tag(v_a_389_) == 0)
{
lean_dec(v_val_387_);
return v___x_388_;
}
else
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_405_; 
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_406_);
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
else
{
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_404_; 
v_val_393_ = lean_ctor_get(v_a_389_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_389_);
if (v_isSharedCheck_404_ == 0)
{
v___x_395_ = v_a_389_;
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_a_389_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Rat_sub(v_val_387_, v_val_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_399_);
v___x_401_ = v___x_391_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
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
}
else
{
lean_dec(v_val_387_);
return v___x_388_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_385_;
}
}
}
}
else
{
uint8_t v___x_407_; 
lean_dec_ref(v___x_344_);
v___x_407_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_305_, v_arg_333_);
lean_dec_ref(v_arg_333_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
v___x_408_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_408_);
v___x_410_ = v___x_321_;
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
else
{
lean_object* v___x_412_; 
lean_del_object(v___x_321_);
v___x_412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
if (lean_obj_tag(v_a_413_) == 0)
{
lean_dec_ref(v_arg_325_);
return v___x_412_;
}
else
{
lean_object* v_val_414_; lean_object* v___x_415_; 
lean_inc_ref(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_val_414_ = lean_ctor_get(v_a_413_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_a_413_, 1);
v___x_415_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
if (lean_obj_tag(v_a_416_) == 0)
{
lean_dec(v_val_414_);
return v___x_415_;
}
else
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_432_; 
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_415_, 0);
lean_dec(v_unused_433_);
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
else
{
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_431_; 
v_val_420_ = lean_ctor_get(v_a_416_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_431_ == 0)
{
v___x_422_ = v_a_416_;
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v_a_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = l_Rat_mul(v_val_414_, v_val_420_);
lean_dec(v_val_414_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_426_);
v___x_428_ = v___x_418_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
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
}
else
{
lean_dec(v_val_414_);
return v___x_415_;
}
}
}
else
{
lean_dec_ref(v_arg_325_);
return v___x_412_;
}
}
}
}
else
{
uint8_t v___x_434_; 
lean_dec_ref(v___x_344_);
v___x_434_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_305_, v_arg_333_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_305_, v_arg_333_);
lean_dec_ref(v_arg_333_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec_ref(v_arg_328_);
lean_dec_ref(v_arg_325_);
v___x_436_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_436_);
v___x_438_ = v___x_321_;
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
lean_object* v___x_440_; 
lean_del_object(v___x_321_);
v___x_440_ = l_Lean_Meta_getNatValue_x3f(v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec_ref(v_arg_328_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_470_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_470_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_470_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_470_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_dec_ref(v_arg_325_);
v___x_445_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
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
else
{
lean_object* v_val_449_; lean_object* v___x_450_; 
lean_del_object(v___x_443_);
v_val_449_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_a_441_, 1);
v___x_450_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
if (lean_obj_tag(v_a_451_) == 0)
{
lean_dec(v_val_449_);
return v___x_450_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_469_);
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_468_;
goto v_resetjp_452_;
}
else
{
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_468_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_467_; 
v_val_455_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_467_ == 0)
{
v___x_457_ = v_a_451_;
v_isShared_458_ = v_isSharedCheck_467_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_a_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_467_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_449_);
v___x_460_ = l_Rat_mul(v___x_459_, v_val_455_);
lean_dec_ref(v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_462_);
v___x_464_ = v___x_453_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
else
{
lean_dec(v_val_449_);
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_arg_325_);
v_a_471_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_440_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_440_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_object* v___x_479_; 
lean_dec_ref(v_arg_333_);
lean_del_object(v___x_321_);
v___x_479_ = l_Lean_Meta_getIntValue_x3f(v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_509_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_509_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_509_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_509_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec_ref(v_arg_325_);
v___x_484_ = lean_box(0);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
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
else
{
lean_object* v_val_488_; lean_object* v___x_489_; 
lean_del_object(v___x_482_);
v_val_488_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_a_480_, 1);
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
if (lean_obj_tag(v_a_490_) == 0)
{
lean_dec(v_val_488_);
return v___x_489_;
}
else
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_489_, 0);
lean_dec(v_unused_508_);
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_507_;
goto v_resetjp_491_;
}
else
{
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_507_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_506_; 
v_val_494_ = lean_ctor_get(v_a_490_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_506_ == 0)
{
v___x_496_ = v_a_490_;
v_isShared_497_ = v_isSharedCheck_506_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_dec(v_a_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_506_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = l_Rat_ofInt(v_val_488_);
v___x_499_ = l_Rat_mul(v___x_498_, v_val_494_);
lean_dec_ref(v___x_498_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_505_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_501_);
v___x_503_ = v___x_492_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
else
{
lean_dec(v_val_488_);
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_arg_325_);
v_a_510_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_479_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_479_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
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
uint8_t v___x_518_; 
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_333_);
v___x_518_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_305_, v_arg_328_);
lean_dec_ref(v_arg_328_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec_ref(v_arg_325_);
v___x_519_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_519_);
v___x_521_ = v___x_321_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v___x_523_; 
lean_del_object(v___x_321_);
v___x_523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_arg_325_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
if (lean_obj_tag(v_a_524_) == 0)
{
return v___x_523_;
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_540_; 
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_541_);
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
else
{
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_540_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_val_528_ = lean_ctor_get(v_a_524_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_524_);
if (v_isSharedCheck_539_ == 0)
{
v___x_530_ = v_a_524_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v_a_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Rat_neg(v_val_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_534_);
v___x_536_ = v___x_526_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
else
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_321_);
v___x_542_ = l_Lean_Meta_getNatValue_x3f(v_arg_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec_ref(v_arg_328_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_563_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_563_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
if (lean_obj_tag(v_a_543_) == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_box(0);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v_val_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_562_; 
v_val_551_ = lean_ctor_get(v_a_543_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_562_ == 0)
{
v___x_553_ = v_a_543_;
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_val_551_);
lean_dec(v_a_543_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_557_);
v___x_559_ = v___x_545_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_542_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_542_);
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
}
else
{
uint8_t v___x_572_; 
lean_dec_ref(v___x_329_);
lean_dec_ref(v_arg_328_);
v___x_572_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_305_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = lean_box(0);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_573_);
v___x_575_ = v___x_321_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_577_);
v___x_579_ = v___x_321_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_318_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_318_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_305_ = stack[0].m_obj;
lean_object* v_model_306_ = stack[1].m_obj;
lean_object* v_e_307_ = stack[2].m_obj;
lean_object* v_a_308_ = stack[3].m_obj;
lean_object* v_a_309_ = stack[4].m_obj;
lean_object* v_a_310_ = stack[5].m_obj;
lean_object* v_a_311_ = stack[6].m_obj;
lean_object* v_res_590_;
v_res_590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_305_, v_model_306_, v_e_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_591_, lean_object* v_model_592_, lean_object* v_e_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_591_, v_model_592_, v_e_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec_ref(v_model_592_);
lean_dec_ref(v_s_591_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_600_, lean_object* v_m_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_601_, v_a_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_604_, v_m_605_, v_a_606_);
lean_dec_ref(v_a_606_);
lean_dec_ref(v_m_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_nat_to_int(v_a_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_610_, lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_614_, lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_614_, v_a_615_, v_x_616_);
lean_dec(v_x_616_);
lean_dec_ref(v_a_615_);
return v_res_617_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_618_, lean_object* v_s_619_, lean_object* v_model_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_619_, v_model_620_, v_e_618_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
return v___x_626_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_618_ = stack[0].m_obj;
lean_object* v_s_619_ = stack[1].m_obj;
lean_object* v_model_620_ = stack[2].m_obj;
lean_object* v_a_621_ = stack[3].m_obj;
lean_object* v_a_622_ = stack[4].m_obj;
lean_object* v_a_623_ = stack[5].m_obj;
lean_object* v_a_624_ = stack[6].m_obj;
lean_object* v_res_627_;
v_res_627_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_618_, v_s_619_, v_model_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_628_, lean_object* v_s_629_, lean_object* v_model_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_628_, v_s_629_, v_model_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec_ref(v_model_630_);
lean_dec_ref(v_s_629_);
return v_res_636_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
else
{
lean_object* v_key_640_; lean_object* v_tail_641_; uint8_t v___x_642_; 
v_key_640_ = lean_ctor_get(v_x_638_, 0);
v_tail_641_ = lean_ctor_get(v_x_638_, 2);
v___x_642_ = lean_expr_eqv(v_key_640_, v_a_637_);
if (v___x_642_ == 0)
{
v_x_638_ = v_tail_641_;
goto _start;
}
else
{
return v___x_642_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_637_ = stack[0].m_obj;
lean_object* v_x_638_ = stack[1].m_obj;
uint8_t v_res_644_;
v_res_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_637_, v_x_638_);
stack->m_num = v_res_644_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_645_, lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_645_, v_x_646_);
lean_dec(v_x_646_);
lean_dec_ref(v_a_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_buckets_651_; lean_object* v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v_fold_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_buckets_651_ = lean_ctor_get(v_m_649_, 1);
v___x_652_ = lean_array_get_size(v_buckets_651_);
v___x_653_ = l_Lean_Expr_hash(v_a_650_);
v___x_654_ = 32ULL;
v___x_655_ = lean_uint64_shift_right(v___x_653_, v___x_654_);
v_fold_656_ = lean_uint64_xor(v___x_653_, v___x_655_);
v___x_657_ = 16ULL;
v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = lean_usize_of_nat(v___x_652_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
v___x_665_ = lean_array_uget_borrowed(v_buckets_651_, v___x_664_);
v___x_666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_650_, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_649_ = stack[0].m_obj;
lean_object* v_a_650_ = stack[1].m_obj;
uint8_t v_res_667_;
v_res_667_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_649_, v_a_650_);
stack->m_num = v_res_667_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_668_, lean_object* v_a_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_668_, v_a_669_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v_m_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v_structId_672_, lean_object* v___x_673_, lean_object* v_goal_674_, lean_object* v_as_675_, size_t v_sz_676_, size_t v_i_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_677_, v_sz_676_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_678_);
return v___x_685_;
}
else
{
lean_object* v_snd_686_; lean_object* v_a_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_716_; 
v_snd_686_ = lean_ctor_get(v_b_678_, 1);
lean_inc(v_snd_686_);
lean_dec_ref(v_b_678_);
v_a_687_ = lean_array_uget(v_as_675_, v_i_677_);
v_fst_688_ = lean_ctor_get(v_a_687_, 0);
v_snd_689_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_716_ == 0)
{
v___x_691_ = v_a_687_;
v_isShared_692_ = v_isSharedCheck_716_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_a_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_716_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_a_695_; uint8_t v___x_702_; 
v___x_693_ = lean_box(0);
v___x_702_ = lean_nat_dec_eq(v_structId_672_, v_snd_689_);
lean_dec(v_snd_689_);
if (v___x_702_ == 0)
{
lean_dec(v_fst_688_);
v_a_695_ = v_snd_686_;
goto v___jp_694_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_686_, v_fst_688_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_inc(v_fst_688_);
v___x_704_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_673_, v_snd_686_, v_fst_688_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_706_; lean_object* v___x_707_; 
v_val_706_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_a_705_, 1);
v___x_707_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_674_, v_fst_688_, v_val_706_, v_snd_686_);
v_a_695_ = v___x_707_;
goto v___jp_694_;
}
else
{
lean_dec(v_a_705_);
lean_dec(v_fst_688_);
v_a_695_ = v_snd_686_;
goto v___jp_694_;
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_del_object(v___x_691_);
lean_dec(v_fst_688_);
lean_dec(v_snd_686_);
v_a_708_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_704_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_704_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_dec(v_fst_688_);
v_a_695_ = v_snd_686_;
goto v___jp_694_;
}
}
v___jp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_a_695_);
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_695_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
size_t v___x_698_; size_t v___x_699_; 
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_677_, v___x_698_);
v_i_677_ = v___x_699_;
v_b_678_ = v___x_697_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_672_ = stack[0].m_obj;
lean_object* v___x_673_ = stack[1].m_obj;
lean_object* v_goal_674_ = stack[2].m_obj;
lean_object* v_as_675_ = stack[3].m_obj;
size_t v_sz_676_ = stack[4].m_num;
size_t v_i_677_ = stack[5].m_num;
lean_object* v_b_678_ = stack[6].m_obj;
lean_object* v___y_679_ = stack[7].m_obj;
lean_object* v___y_680_ = stack[8].m_obj;
lean_object* v___y_681_ = stack[9].m_obj;
lean_object* v___y_682_ = stack[10].m_obj;
lean_object* v_res_717_;
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_672_, v___x_673_, v_goal_674_, v_as_675_, v_sz_676_, v_i_677_, v_b_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_structId_718_, lean_object* v___x_719_, lean_object* v_goal_720_, lean_object* v_as_721_, lean_object* v_sz_722_, lean_object* v_i_723_, lean_object* v_b_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
size_t v_sz_boxed_730_; size_t v_i_boxed_731_; lean_object* v_res_732_; 
v_sz_boxed_730_ = lean_unbox_usize(v_sz_722_);
lean_dec(v_sz_722_);
v_i_boxed_731_ = lean_unbox_usize(v_i_723_);
lean_dec(v_i_723_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_718_, v___x_719_, v_goal_720_, v_as_721_, v_sz_boxed_730_, v_i_boxed_731_, v_b_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec_ref(v_as_721_);
lean_dec_ref(v_goal_720_);
lean_dec_ref(v___x_719_);
lean_dec(v_structId_718_);
return v_res_732_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v_structId_733_, lean_object* v___x_734_, lean_object* v_goal_735_, lean_object* v_as_736_, size_t v_sz_737_, size_t v_i_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_738_, v_sz_737_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_b_739_);
return v___x_746_;
}
else
{
lean_object* v_snd_747_; lean_object* v_a_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_777_; 
v_snd_747_ = lean_ctor_get(v_b_739_, 1);
lean_inc(v_snd_747_);
lean_dec_ref(v_b_739_);
v_a_748_ = lean_array_uget(v_as_736_, v_i_738_);
v_fst_749_ = lean_ctor_get(v_a_748_, 0);
v_snd_750_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_777_ == 0)
{
v___x_752_ = v_a_748_;
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_inc(v_fst_749_);
lean_dec(v_a_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v_a_756_; uint8_t v___x_763_; 
v___x_754_ = lean_box(0);
v___x_763_ = lean_nat_dec_eq(v_structId_733_, v_snd_750_);
lean_dec(v_snd_750_);
if (v___x_763_ == 0)
{
lean_dec(v_fst_749_);
v_a_756_ = v_snd_747_;
goto v___jp_755_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_747_, v_fst_749_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_inc(v_fst_749_);
v___x_765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_734_, v_snd_747_, v_fst_749_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v_a_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_a_766_, 1);
v___x_768_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_735_, v_fst_749_, v_val_767_, v_snd_747_);
v_a_756_ = v___x_768_;
goto v___jp_755_;
}
else
{
lean_dec(v_a_766_);
lean_dec(v_fst_749_);
v_a_756_ = v_snd_747_;
goto v___jp_755_;
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_del_object(v___x_752_);
lean_dec(v_fst_749_);
lean_dec(v_snd_747_);
v_a_769_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_765_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_dec(v_fst_749_);
v_a_756_ = v_snd_747_;
goto v___jp_755_;
}
}
v___jp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v_a_756_);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_756_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_add(v_i_738_, v___x_759_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_733_, v___x_734_, v_goal_735_, v_as_736_, v_sz_737_, v___x_760_, v___x_758_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_733_ = stack[0].m_obj;
lean_object* v___x_734_ = stack[1].m_obj;
lean_object* v_goal_735_ = stack[2].m_obj;
lean_object* v_as_736_ = stack[3].m_obj;
size_t v_sz_737_ = stack[4].m_num;
size_t v_i_738_ = stack[5].m_num;
lean_object* v_b_739_ = stack[6].m_obj;
lean_object* v___y_740_ = stack[7].m_obj;
lean_object* v___y_741_ = stack[8].m_obj;
lean_object* v___y_742_ = stack[9].m_obj;
lean_object* v___y_743_ = stack[10].m_obj;
lean_object* v_res_778_;
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_733_, v___x_734_, v_goal_735_, v_as_736_, v_sz_737_, v_i_738_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
stack->m_obj
 = v_res_778_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v_structId_779_, lean_object* v___x_780_, lean_object* v_goal_781_, lean_object* v_as_782_, lean_object* v_sz_783_, lean_object* v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
size_t v_sz_boxed_791_; size_t v_i_boxed_792_; lean_object* v_res_793_; 
v_sz_boxed_791_ = lean_unbox_usize(v_sz_783_);
lean_dec(v_sz_783_);
v_i_boxed_792_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_779_, v___x_780_, v_goal_781_, v_as_782_, v_sz_boxed_791_, v_i_boxed_792_, v_b_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_as_782_);
lean_dec_ref(v_goal_781_);
lean_dec_ref(v___x_780_);
lean_dec(v_structId_779_);
return v_res_793_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_794_, lean_object* v_structId_795_, lean_object* v___x_796_, lean_object* v_goal_797_, lean_object* v_n_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
if (lean_obj_tag(v_n_798_) == 0)
{
lean_object* v_cs_805_; lean_object* v___x_806_; lean_object* v___x_807_; size_t v_sz_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_cs_805_ = lean_ctor_get(v_n_798_, 0);
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_b_799_);
v_sz_808_ = lean_array_size(v_cs_805_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_794_, v_structId_795_, v___x_796_, v_goal_797_, v_cs_805_, v_sz_808_, v___x_809_, v___x_807_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_825_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_825_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_fst_815_; 
v_fst_815_ = lean_ctor_get(v_a_811_, 0);
if (lean_obj_tag(v_fst_815_) == 0)
{
lean_object* v_snd_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v_snd_816_ = lean_ctor_get(v_a_811_, 1);
lean_inc(v_snd_816_);
lean_dec(v_a_811_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_snd_816_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; 
lean_inc_ref(v_fst_815_);
lean_dec(v_a_811_);
v_val_821_ = lean_ctor_get(v_fst_815_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_fst_815_, 1);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_val_821_);
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_val_821_);
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
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_810_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_810_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_vs_834_ = lean_ctor_get(v_n_798_, 0);
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_b_799_);
v_sz_837_ = lean_array_size(v_vs_834_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_795_, v___x_796_, v_goal_797_, v_vs_834_, v_sz_837_, v___x_838_, v___x_836_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_854_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_854_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fst_844_; 
v_fst_844_ = lean_ctor_get(v_a_840_, 0);
if (lean_obj_tag(v_fst_844_) == 0)
{
lean_object* v_snd_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v_snd_845_ = lean_ctor_get(v_a_840_, 1);
lean_inc(v_snd_845_);
lean_dec(v_a_840_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_snd_845_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_846_);
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v_val_850_; lean_object* v___x_852_; 
lean_inc_ref(v_fst_844_);
lean_dec(v_a_840_);
v_val_850_ = lean_ctor_get(v_fst_844_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_fst_844_, 1);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_val_850_);
v___x_852_ = v___x_842_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_val_850_);
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
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_839_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_839_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_794_ = stack[0].m_obj;
lean_object* v_structId_795_ = stack[1].m_obj;
lean_object* v___x_796_ = stack[2].m_obj;
lean_object* v_goal_797_ = stack[3].m_obj;
lean_object* v_n_798_ = stack[4].m_obj;
lean_object* v_b_799_ = stack[5].m_obj;
lean_object* v___y_800_ = stack[6].m_obj;
lean_object* v___y_801_ = stack[7].m_obj;
lean_object* v___y_802_ = stack[8].m_obj;
lean_object* v___y_803_ = stack[9].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_794_, v_structId_795_, v___x_796_, v_goal_797_, v_n_798_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_863_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_864_, lean_object* v_structId_865_, lean_object* v___x_866_, lean_object* v_goal_867_, lean_object* v_as_868_, size_t v_sz_869_, size_t v_i_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_870_, v_sz_869_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_b_871_);
return v___x_878_;
}
else
{
lean_object* v_snd_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_913_; 
v_snd_879_ = lean_ctor_get(v_b_871_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_b_871_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_b_871_, 0);
lean_dec(v_unused_914_);
v___x_881_ = v_b_871_;
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snd_879_);
lean_dec(v_b_871_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v_a_884_ = lean_array_uget_borrowed(v_as_868_, v_i_870_);
lean_inc(v_snd_879_);
v___x_885_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_864_, v_structId_865_, v___x_866_, v_goal_867_, v_a_884_, v_snd_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_904_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 0)
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_a_886_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_890_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_879_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_892_);
v___x_894_ = v___x_888_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; 
lean_del_object(v___x_888_);
lean_dec(v_snd_879_);
v_a_897_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v_a_886_, 1);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_a_897_);
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_899_ = v___x_881_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
size_t v___x_900_; size_t v___x_901_; 
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_870_, v___x_900_);
v_i_870_ = v___x_901_;
v_b_871_ = v___x_899_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_881_);
lean_dec(v_snd_879_);
v_a_905_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_885_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_864_ = stack[0].m_obj;
lean_object* v_structId_865_ = stack[1].m_obj;
lean_object* v___x_866_ = stack[2].m_obj;
lean_object* v_goal_867_ = stack[3].m_obj;
lean_object* v_as_868_ = stack[4].m_obj;
size_t v_sz_869_ = stack[5].m_num;
size_t v_i_870_ = stack[6].m_num;
lean_object* v_b_871_ = stack[7].m_obj;
lean_object* v___y_872_ = stack[8].m_obj;
lean_object* v___y_873_ = stack[9].m_obj;
lean_object* v___y_874_ = stack[10].m_obj;
lean_object* v___y_875_ = stack[11].m_obj;
lean_object* v_res_915_;
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_864_, v_structId_865_, v___x_866_, v_goal_867_, v_as_868_, v_sz_869_, v_i_870_, v_b_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_916_, lean_object* v_structId_917_, lean_object* v___x_918_, lean_object* v_goal_919_, lean_object* v_as_920_, lean_object* v_sz_921_, lean_object* v_i_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_921_);
lean_dec(v_sz_921_);
v_i_boxed_930_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_916_, v_structId_917_, v___x_918_, v_goal_919_, v_as_920_, v_sz_boxed_929_, v_i_boxed_930_, v_b_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_as_920_);
lean_dec_ref(v_goal_919_);
lean_dec_ref(v___x_918_);
lean_dec(v_structId_917_);
lean_dec_ref(v_init_916_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_932_, lean_object* v_structId_933_, lean_object* v___x_934_, lean_object* v_goal_935_, lean_object* v_n_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_932_, v_structId_933_, v___x_934_, v_goal_935_, v_n_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_n_936_);
lean_dec_ref(v_goal_935_);
lean_dec_ref(v___x_934_);
lean_dec(v_structId_933_);
lean_dec_ref(v_init_932_);
return v_res_943_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v_structId_944_, lean_object* v___x_945_, lean_object* v_goal_946_, lean_object* v_as_947_, size_t v_sz_948_, size_t v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v_b_950_);
return v___x_957_;
}
else
{
lean_object* v_snd_958_; lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_988_; 
v_snd_958_ = lean_ctor_get(v_b_950_, 1);
lean_inc(v_snd_958_);
lean_dec_ref(v_b_950_);
v_a_959_ = lean_array_uget(v_as_947_, v_i_949_);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_988_ == 0)
{
v___x_963_ = v_a_959_;
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_inc(v_fst_960_);
lean_dec(v_a_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v_a_967_; uint8_t v___x_974_; 
v___x_965_ = lean_box(0);
v___x_974_ = lean_nat_dec_eq(v_structId_944_, v_snd_961_);
lean_dec(v_snd_961_);
if (v___x_974_ == 0)
{
lean_dec(v_fst_960_);
v_a_967_ = v_snd_958_;
goto v___jp_966_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_958_, v_fst_960_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_inc(v_fst_960_);
v___x_976_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_945_, v_snd_958_, v_fst_960_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
if (lean_obj_tag(v_a_977_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v_a_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_a_977_, 1);
v___x_979_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_946_, v_fst_960_, v_val_978_, v_snd_958_);
v_a_967_ = v___x_979_;
goto v___jp_966_;
}
else
{
lean_dec(v_a_977_);
lean_dec(v_fst_960_);
v_a_967_ = v_snd_958_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_963_);
lean_dec(v_fst_960_);
lean_dec(v_snd_958_);
v_a_980_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_976_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_dec(v_fst_960_);
v_a_967_ = v_snd_958_;
goto v___jp_966_;
}
}
v___jp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_a_967_);
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_967_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
size_t v___x_970_; size_t v___x_971_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_949_, v___x_970_);
v_i_949_ = v___x_971_;
v_b_950_ = v___x_969_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_944_ = stack[0].m_obj;
lean_object* v___x_945_ = stack[1].m_obj;
lean_object* v_goal_946_ = stack[2].m_obj;
lean_object* v_as_947_ = stack[3].m_obj;
size_t v_sz_948_ = stack[4].m_num;
size_t v_i_949_ = stack[5].m_num;
lean_object* v_b_950_ = stack[6].m_obj;
lean_object* v___y_951_ = stack[7].m_obj;
lean_object* v___y_952_ = stack[8].m_obj;
lean_object* v___y_953_ = stack[9].m_obj;
lean_object* v___y_954_ = stack[10].m_obj;
lean_object* v_res_989_;
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_944_, v___x_945_, v_goal_946_, v_as_947_, v_sz_948_, v_i_949_, v_b_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v_structId_990_, lean_object* v___x_991_, lean_object* v_goal_992_, lean_object* v_as_993_, lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
size_t v_sz_boxed_1002_; size_t v_i_boxed_1003_; lean_object* v_res_1004_; 
v_sz_boxed_1002_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_1003_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_990_, v___x_991_, v_goal_992_, v_as_993_, v_sz_boxed_1002_, v_i_boxed_1003_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v_as_993_);
lean_dec_ref(v_goal_992_);
lean_dec_ref(v___x_991_);
lean_dec(v_structId_990_);
return v_res_1004_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v_structId_1005_, lean_object* v___x_1006_, lean_object* v_goal_1007_, lean_object* v_as_1008_, size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1011_);
return v___x_1018_;
}
else
{
lean_object* v_snd_1019_; lean_object* v_a_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1049_; 
v_snd_1019_ = lean_ctor_get(v_b_1011_, 1);
lean_inc(v_snd_1019_);
lean_dec_ref(v_b_1011_);
v_a_1020_ = lean_array_uget(v_as_1008_, v_i_1010_);
v_fst_1021_ = lean_ctor_get(v_a_1020_, 0);
v_snd_1022_ = lean_ctor_get(v_a_1020_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1024_ = v_a_1020_;
v_isShared_1025_ = v_isSharedCheck_1049_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v_a_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1049_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v_a_1028_; uint8_t v___x_1035_; 
v___x_1026_ = lean_box(0);
v___x_1035_ = lean_nat_dec_eq(v_structId_1005_, v_snd_1022_);
lean_dec(v_snd_1022_);
if (v___x_1035_ == 0)
{
lean_dec(v_fst_1021_);
v_a_1028_ = v_snd_1019_;
goto v___jp_1027_;
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_1019_, v_fst_1021_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_inc(v_fst_1021_);
v___x_1037_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_1006_, v_snd_1019_, v_fst_1021_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
if (lean_obj_tag(v_a_1038_) == 1)
{
lean_object* v_val_1039_; lean_object* v___x_1040_; 
v_val_1039_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v_a_1038_, 1);
v___x_1040_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1007_, v_fst_1021_, v_val_1039_, v_snd_1019_);
v_a_1028_ = v___x_1040_;
goto v___jp_1027_;
}
else
{
lean_dec(v_a_1038_);
lean_dec(v_fst_1021_);
v_a_1028_ = v_snd_1019_;
goto v___jp_1027_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_del_object(v___x_1024_);
lean_dec(v_fst_1021_);
lean_dec(v_snd_1019_);
v_a_1041_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1037_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1037_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_dec(v_fst_1021_);
v_a_1028_ = v_snd_1019_;
goto v___jp_1027_;
}
}
v___jp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_a_1028_);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1028_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1010_, v___x_1031_);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_1005_, v___x_1006_, v_goal_1007_, v_as_1008_, v_sz_1009_, v___x_1032_, v___x_1030_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1033_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_1005_ = stack[0].m_obj;
lean_object* v___x_1006_ = stack[1].m_obj;
lean_object* v_goal_1007_ = stack[2].m_obj;
lean_object* v_as_1008_ = stack[3].m_obj;
size_t v_sz_1009_ = stack[4].m_num;
size_t v_i_1010_ = stack[5].m_num;
lean_object* v_b_1011_ = stack[6].m_obj;
lean_object* v___y_1012_ = stack[7].m_obj;
lean_object* v___y_1013_ = stack[8].m_obj;
lean_object* v___y_1014_ = stack[9].m_obj;
lean_object* v___y_1015_ = stack[10].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1005_, v___x_1006_, v_goal_1007_, v_as_1008_, v_sz_1009_, v_i_1010_, v_b_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v_structId_1051_, lean_object* v___x_1052_, lean_object* v_goal_1053_, lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1051_, v___x_1052_, v_goal_1053_, v_as_1054_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_as_1054_);
lean_dec_ref(v_goal_1053_);
lean_dec_ref(v___x_1052_);
lean_dec(v_structId_1051_);
return v_res_1065_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v_structId_1066_, lean_object* v___x_1067_, lean_object* v_goal_1068_, lean_object* v_t_1069_, lean_object* v_init_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_root_1076_; lean_object* v_tail_1077_; lean_object* v___x_1078_; 
v_root_1076_ = lean_ctor_get(v_t_1069_, 0);
v_tail_1077_ = lean_ctor_get(v_t_1069_, 1);
lean_inc_ref(v_init_1070_);
v___x_1078_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1070_, v_structId_1066_, v___x_1067_, v_goal_1068_, v_root_1076_, v_init_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec_ref(v_init_1070_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1115_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1115_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1115_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
if (lean_obj_tag(v_a_1079_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; 
v_a_1083_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_a_1079_, 1);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_a_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v_sz_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
lean_del_object(v___x_1081_);
v_a_1087_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_a_1079_, 1);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1087_);
v_sz_1090_ = lean_array_size(v_tail_1077_);
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1066_, v___x_1067_, v_goal_1068_, v_tail_1077_, v_sz_1090_, v___x_1091_, v___x_1089_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_fst_1097_; 
v_fst_1097_ = lean_ctor_get(v_a_1093_, 0);
if (lean_obj_tag(v_fst_1097_) == 0)
{
lean_object* v_snd_1098_; lean_object* v___x_1100_; 
v_snd_1098_ = lean_ctor_get(v_a_1093_, 1);
lean_inc(v_snd_1098_);
lean_dec(v_a_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_snd_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_snd_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v_val_1102_; lean_object* v___x_1104_; 
lean_inc_ref(v_fst_1097_);
lean_dec(v_a_1093_);
v_val_1102_ = lean_ctor_get(v_fst_1097_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v_fst_1097_, 1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_val_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_val_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1092_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1078_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1078_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_1066_ = stack[0].m_obj;
lean_object* v___x_1067_ = stack[1].m_obj;
lean_object* v_goal_1068_ = stack[2].m_obj;
lean_object* v_t_1069_ = stack[3].m_obj;
lean_object* v_init_1070_ = stack[4].m_obj;
lean_object* v___y_1071_ = stack[5].m_obj;
lean_object* v___y_1072_ = stack[6].m_obj;
lean_object* v___y_1073_ = stack[7].m_obj;
lean_object* v___y_1074_ = stack[8].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1066_, v___x_1067_, v_goal_1068_, v_t_1069_, v_init_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v_structId_1125_, lean_object* v___x_1126_, lean_object* v_goal_1127_, lean_object* v_t_1128_, lean_object* v_init_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1125_, v___x_1126_, v_goal_1127_, v_t_1128_, v_init_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_t_1128_);
lean_dec_ref(v_goal_1127_);
lean_dec_ref(v___x_1126_);
lean_dec(v_structId_1125_);
return v_res_1135_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1136_, lean_object* v_structId_1137_, lean_object* v_model_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_ref_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_ref_1144_ = lean_ctor_get(v_a_1141_, 2);
v___x_1145_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1146_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1147_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1146_, v_goal_1136_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v_structs_1149_; lean_object* v_exprToStructIdEntries_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v_structs_1149_ = lean_ctor_get(v_a_1148_, 0);
lean_inc_ref(v_structs_1149_);
v_exprToStructIdEntries_1150_ = lean_ctor_get(v_a_1148_, 3);
lean_inc_ref(v_exprToStructIdEntries_1150_);
lean_dec(v_a_1148_);
v___x_1151_ = lean_array_get(v___x_1145_, v_structs_1149_, v_structId_1137_);
lean_dec_ref(v_structs_1149_);
v___x_1152_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1137_, v___x_1151_, v_goal_1136_, v_exprToStructIdEntries_1150_, v_model_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec_ref(v_exprToStructIdEntries_1150_);
lean_dec(v___x_1151_);
return v___x_1152_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_model_1138_);
v_a_1153_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1155_ = v___x_1147_;
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1164_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1157_ = lean_io_error_to_string(v_a_1153_);
v___x_1158_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
v___x_1159_ = l_Lean_MessageData_ofFormat(v___x_1158_);
lean_inc(v_ref_1144_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_ref_1144_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1160_);
v___x_1162_ = v___x_1155_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1136_ = stack[0].m_obj;
lean_object* v_structId_1137_ = stack[1].m_obj;
lean_object* v_model_1138_ = stack[2].m_obj;
lean_object* v_a_1139_ = stack[3].m_obj;
lean_object* v_a_1140_ = stack[4].m_obj;
lean_object* v_a_1141_ = stack[5].m_obj;
lean_object* v_a_1142_ = stack[6].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1136_, v_structId_1137_, v_model_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
stack->m_obj
 = v_res_1165_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1166_, lean_object* v_structId_1167_, lean_object* v_model_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1166_, v_structId_1167_, v_model_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_structId_1167_);
lean_dec_ref(v_goal_1166_);
return v_res_1174_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1175_, lean_object* v_m_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1176_, v_a_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1176_ = stack[1].m_obj;
lean_object* v_a_1177_ = stack[2].m_obj;
uint8_t v_res_1179_;
v_res_1179_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_box(0), v_m_1176_, v_a_1177_);
stack->m_num = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1180_, lean_object* v_m_1181_, lean_object* v_a_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1180_, v_m_1181_, v_a_1182_);
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_m_1181_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1185_, lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1186_, v_x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1186_ = stack[1].m_obj;
lean_object* v_x_1187_ = stack[2].m_obj;
uint8_t v_res_1189_;
v_res_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_box(0), v_a_1186_, v_x_1187_);
stack->m_num = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1190_, lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
uint8_t v_res_1193_; lean_object* v_r_1194_; 
v_res_1193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1190_, v_a_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec_ref(v_a_1191_);
v_r_1194_ = lean_box(v_res_1193_);
return v_r_1194_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1195_, lean_object* v___x_1196_, lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref(v___x_1196_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_b_1200_);
return v___x_1207_;
}
else
{
lean_object* v_snd_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1249_; 
v_snd_1208_ = lean_ctor_get(v_b_1200_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_b_1200_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_b_1200_, 0);
lean_dec(v_unused_1250_);
v___x_1210_ = v_b_1200_;
v_isShared_1211_ = v_isSharedCheck_1249_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_snd_1208_);
lean_dec(v_b_1200_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1249_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v_a_1214_; lean_object* v_a_1221_; lean_object* v___x_1222_; 
v___x_1212_ = lean_box(0);
v_a_1221_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
lean_inc(v_a_1221_);
v___x_1222_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1195_, v_a_1221_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; uint8_t v___x_1224_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1223_);
if (v___x_1224_ == 0)
{
lean_dec(v_a_1223_);
v_a_1214_ = v_snd_1208_;
goto v___jp_1213_;
}
else
{
lean_object* v_type_1225_; lean_object* v___x_1226_; 
v_type_1225_ = lean_ctor_get(v___x_1196_, 2);
lean_inc(v_a_1223_);
lean_inc_ref(v_type_1225_);
v___x_1226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1225_, v_a_1223_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; uint8_t v___x_1228_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = lean_unbox(v_a_1227_);
lean_dec(v_a_1227_);
if (v___x_1228_ == 0)
{
lean_dec(v_a_1223_);
v_a_1214_ = v_snd_1208_;
goto v___jp_1213_;
}
else
{
lean_object* v_self_1229_; lean_object* v___x_1230_; 
v_self_1229_ = lean_ctor_get(v_a_1223_, 0);
lean_inc_ref(v_self_1229_);
lean_dec(v_a_1223_);
v___x_1230_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1196_, v_self_1229_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1195_, v_self_1229_, v_val_1231_, v_snd_1208_);
v_a_1214_ = v___x_1232_;
goto v___jp_1213_;
}
else
{
lean_dec(v___x_1230_);
lean_dec_ref(v_self_1229_);
v_a_1214_ = v_snd_1208_;
goto v___jp_1213_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1223_);
lean_del_object(v___x_1210_);
lean_dec(v_snd_1208_);
lean_dec_ref(v___x_1196_);
v_a_1233_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1226_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1226_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1210_);
lean_dec(v_snd_1208_);
lean_dec_ref(v___x_1196_);
v_a_1241_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1222_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1222_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
v___jp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v_a_1214_);
lean_ctor_set(v___x_1210_, 0, v___x_1212_);
v___x_1216_ = v___x_1210_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1214_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1199_, v___x_1217_);
v_i_1199_ = v___x_1218_;
v_b_1200_ = v___x_1216_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1195_ = stack[0].m_obj;
lean_object* v___x_1196_ = stack[1].m_obj;
lean_object* v_as_1197_ = stack[2].m_obj;
size_t v_sz_1198_ = stack[3].m_num;
size_t v_i_1199_ = stack[4].m_num;
lean_object* v_b_1200_ = stack[5].m_obj;
lean_object* v___y_1201_ = stack[6].m_obj;
lean_object* v___y_1202_ = stack[7].m_obj;
lean_object* v___y_1203_ = stack[8].m_obj;
lean_object* v___y_1204_ = stack[9].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1195_, v___x_1196_, v_as_1197_, v_sz_1198_, v_i_1199_, v_b_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1252_, lean_object* v___x_1253_, lean_object* v_as_1254_, lean_object* v_sz_1255_, lean_object* v_i_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
size_t v_sz_boxed_1263_; size_t v_i_boxed_1264_; lean_object* v_res_1265_; 
v_sz_boxed_1263_ = lean_unbox_usize(v_sz_1255_);
lean_dec(v_sz_1255_);
v_i_boxed_1264_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1252_, v___x_1253_, v_as_1254_, v_sz_boxed_1263_, v_i_boxed_1264_, v_b_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v_as_1254_);
lean_dec_ref(v_goal_1252_);
return v_res_1265_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1266_, lean_object* v___x_1267_, lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec_ref(v___x_1267_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_b_1271_);
return v___x_1278_;
}
else
{
lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1320_; 
v_snd_1279_ = lean_ctor_get(v_b_1271_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_b_1271_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_b_1271_, 0);
lean_dec(v_unused_1321_);
v___x_1281_ = v_b_1271_;
v_isShared_1282_ = v_isSharedCheck_1320_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_dec(v_b_1271_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1320_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v_a_1285_; lean_object* v_a_1292_; lean_object* v___x_1293_; 
v___x_1283_ = lean_box(0);
v_a_1292_ = lean_array_uget_borrowed(v_as_1268_, v_i_1270_);
lean_inc(v_a_1292_);
v___x_1293_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1266_, v_a_1292_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; uint8_t v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1294_);
if (v___x_1295_ == 0)
{
lean_dec(v_a_1294_);
v_a_1285_ = v_snd_1279_;
goto v___jp_1284_;
}
else
{
lean_object* v_type_1296_; lean_object* v___x_1297_; 
v_type_1296_ = lean_ctor_get(v___x_1267_, 2);
lean_inc(v_a_1294_);
lean_inc_ref(v_type_1296_);
v___x_1297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1296_, v_a_1294_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; uint8_t v___x_1299_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = lean_unbox(v_a_1298_);
lean_dec(v_a_1298_);
if (v___x_1299_ == 0)
{
lean_dec(v_a_1294_);
v_a_1285_ = v_snd_1279_;
goto v___jp_1284_;
}
else
{
lean_object* v_self_1300_; lean_object* v___x_1301_; 
v_self_1300_ = lean_ctor_get(v_a_1294_, 0);
lean_inc_ref(v_self_1300_);
lean_dec(v_a_1294_);
v___x_1301_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1267_, v_self_1300_);
if (lean_obj_tag(v___x_1301_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1303_; 
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1303_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1266_, v_self_1300_, v_val_1302_, v_snd_1279_);
v_a_1285_ = v___x_1303_;
goto v___jp_1284_;
}
else
{
lean_dec(v___x_1301_);
lean_dec_ref(v_self_1300_);
v_a_1285_ = v_snd_1279_;
goto v___jp_1284_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1294_);
lean_del_object(v___x_1281_);
lean_dec(v_snd_1279_);
lean_dec_ref(v___x_1267_);
v_a_1304_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1297_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1297_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1281_);
lean_dec(v_snd_1279_);
lean_dec_ref(v___x_1267_);
v_a_1312_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1293_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1293_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
v___jp_1284_:
{
lean_object* v___x_1287_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v_a_1285_);
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1287_ = v___x_1281_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_a_1285_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_add(v_i_1270_, v___x_1288_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1266_, v___x_1267_, v_as_1268_, v_sz_1269_, v___x_1289_, v___x_1287_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1290_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1266_ = stack[0].m_obj;
lean_object* v___x_1267_ = stack[1].m_obj;
lean_object* v_as_1268_ = stack[2].m_obj;
size_t v_sz_1269_ = stack[3].m_num;
size_t v_i_1270_ = stack[4].m_num;
lean_object* v_b_1271_ = stack[5].m_obj;
lean_object* v___y_1272_ = stack[6].m_obj;
lean_object* v___y_1273_ = stack[7].m_obj;
lean_object* v___y_1274_ = stack[8].m_obj;
lean_object* v___y_1275_ = stack[9].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1266_, v___x_1267_, v_as_1268_, v_sz_1269_, v_i_1270_, v_b_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1323_, lean_object* v___x_1324_, lean_object* v_as_1325_, lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1323_, v___x_1324_, v_as_1325_, v_sz_boxed_1334_, v_i_boxed_1335_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec_ref(v_as_1325_);
lean_dec_ref(v_goal_1323_);
return v_res_1336_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1337_, lean_object* v_goal_1338_, lean_object* v___x_1339_, lean_object* v_n_1340_, lean_object* v_b_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
if (lean_obj_tag(v_n_1340_) == 0)
{
lean_object* v_cs_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_cs_1347_ = lean_ctor_get(v_n_1340_, 0);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_b_1341_);
v_sz_1350_ = lean_array_size(v_cs_1347_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1337_, v_goal_1338_, v___x_1339_, v_cs_1347_, v_sz_1350_, v___x_1351_, v___x_1349_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
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
else
{
lean_object* v_vs_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v_vs_1376_ = lean_ctor_get(v_n_1340_, 0);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_b_1341_);
v_sz_1379_ = lean_array_size(v_vs_1376_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1338_, v___x_1339_, v_vs_1376_, v_sz_1379_, v___x_1380_, v___x_1378_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1396_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_fst_1386_; 
v_fst_1386_ = lean_ctor_get(v_a_1382_, 0);
if (lean_obj_tag(v_fst_1386_) == 0)
{
lean_object* v_snd_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v_snd_1387_ = lean_ctor_get(v_a_1382_, 1);
lean_inc(v_snd_1387_);
lean_dec(v_a_1382_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_snd_1387_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v_val_1392_; lean_object* v___x_1394_; 
lean_inc_ref(v_fst_1386_);
lean_dec(v_a_1382_);
v_val_1392_ = lean_ctor_get(v_fst_1386_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v_fst_1386_, 1);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_val_1392_);
v___x_1394_ = v___x_1384_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_val_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1381_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1381_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1337_ = stack[0].m_obj;
lean_object* v_goal_1338_ = stack[1].m_obj;
lean_object* v___x_1339_ = stack[2].m_obj;
lean_object* v_n_1340_ = stack[3].m_obj;
lean_object* v_b_1341_ = stack[4].m_obj;
lean_object* v___y_1342_ = stack[5].m_obj;
lean_object* v___y_1343_ = stack[6].m_obj;
lean_object* v___y_1344_ = stack[7].m_obj;
lean_object* v___y_1345_ = stack[8].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1337_, v_goal_1338_, v___x_1339_, v_n_1340_, v_b_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
stack->m_obj
 = v_res_1405_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1406_, lean_object* v_goal_1407_, lean_object* v___x_1408_, lean_object* v_as_1409_, size_t v_sz_1410_, size_t v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
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
lean_object* v___x_1424_; lean_object* v_a_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(0);
v_a_1425_ = lean_array_uget_borrowed(v_as_1409_, v_i_1411_);
lean_inc(v_snd_1420_);
lean_inc_ref(v___x_1408_);
v___x_1426_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1406_, v_goal_1407_, v___x_1408_, v_a_1425_, v_snd_1420_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1445_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1445_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1445_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
if (lean_obj_tag(v_a_1427_) == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec_ref(v___x_1408_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_a_1427_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1431_);
v___x_1433_ = v___x_1422_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_snd_1420_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1433_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; 
lean_del_object(v___x_1429_);
lean_dec(v_snd_1420_);
v_a_1438_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v_a_1427_, 1);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v_a_1438_);
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1440_ = v___x_1422_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1438_);
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
v_a_1446_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1426_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1426_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1406_ = stack[0].m_obj;
lean_object* v_goal_1407_ = stack[1].m_obj;
lean_object* v___x_1408_ = stack[2].m_obj;
lean_object* v_as_1409_ = stack[3].m_obj;
size_t v_sz_1410_ = stack[4].m_num;
size_t v_i_1411_ = stack[5].m_num;
lean_object* v_b_1412_ = stack[6].m_obj;
lean_object* v___y_1413_ = stack[7].m_obj;
lean_object* v___y_1414_ = stack[8].m_obj;
lean_object* v___y_1415_ = stack[9].m_obj;
lean_object* v___y_1416_ = stack[10].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1406_, v_goal_1407_, v___x_1408_, v_as_1409_, v_sz_1410_, v_i_1411_, v_b_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1457_, lean_object* v_goal_1458_, lean_object* v___x_1459_, lean_object* v_as_1460_, lean_object* v_sz_1461_, lean_object* v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
size_t v_sz_boxed_1469_; size_t v_i_boxed_1470_; lean_object* v_res_1471_; 
v_sz_boxed_1469_ = lean_unbox_usize(v_sz_1461_);
lean_dec(v_sz_1461_);
v_i_boxed_1470_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1457_, v_goal_1458_, v___x_1459_, v_as_1460_, v_sz_boxed_1469_, v_i_boxed_1470_, v_b_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec_ref(v_as_1460_);
lean_dec_ref(v_goal_1458_);
lean_dec_ref(v_init_1457_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1472_, lean_object* v_goal_1473_, lean_object* v___x_1474_, lean_object* v_n_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1472_, v_goal_1473_, v___x_1474_, v_n_1475_, v_b_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v_n_1475_);
lean_dec_ref(v_goal_1473_);
lean_dec_ref(v_init_1472_);
return v_res_1482_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1483_, lean_object* v___x_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref(v___x_1484_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1488_);
return v___x_1495_;
}
else
{
lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1537_; 
v_snd_1496_ = lean_ctor_get(v_b_1488_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_b_1488_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_b_1488_, 0);
lean_dec(v_unused_1538_);
v___x_1498_ = v_b_1488_;
v_isShared_1499_ = v_isSharedCheck_1537_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_dec(v_b_1488_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1537_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v_a_1502_; lean_object* v_a_1509_; lean_object* v___x_1510_; 
v___x_1500_ = lean_box(0);
v_a_1509_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
lean_inc(v_a_1509_);
v___x_1510_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1483_, v_a_1509_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; uint8_t v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1511_);
if (v___x_1512_ == 0)
{
lean_dec(v_a_1511_);
v_a_1502_ = v_snd_1496_;
goto v___jp_1501_;
}
else
{
lean_object* v_type_1513_; lean_object* v___x_1514_; 
v_type_1513_ = lean_ctor_get(v___x_1484_, 2);
lean_inc(v_a_1511_);
lean_inc_ref(v_type_1513_);
v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1513_, v_a_1511_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; uint8_t v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_unbox(v_a_1515_);
lean_dec(v_a_1515_);
if (v___x_1516_ == 0)
{
lean_dec(v_a_1511_);
v_a_1502_ = v_snd_1496_;
goto v___jp_1501_;
}
else
{
lean_object* v_self_1517_; lean_object* v___x_1518_; 
v_self_1517_ = lean_ctor_get(v_a_1511_, 0);
lean_inc_ref(v_self_1517_);
lean_dec(v_a_1511_);
v___x_1518_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1484_, v_self_1517_);
if (lean_obj_tag(v___x_1518_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1520_; 
v_val_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1483_, v_self_1517_, v_val_1519_, v_snd_1496_);
v_a_1502_ = v___x_1520_;
goto v___jp_1501_;
}
else
{
lean_dec(v___x_1518_);
lean_dec_ref(v_self_1517_);
v_a_1502_ = v_snd_1496_;
goto v___jp_1501_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_a_1511_);
lean_del_object(v___x_1498_);
lean_dec(v_snd_1496_);
lean_dec_ref(v___x_1484_);
v_a_1521_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1514_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1514_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_del_object(v___x_1498_);
lean_dec(v_snd_1496_);
lean_dec_ref(v___x_1484_);
v_a_1529_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1510_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1510_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
v___jp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_a_1502_);
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_a_1502_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
size_t v___x_1505_; size_t v___x_1506_; 
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1487_, v___x_1505_);
v_i_1487_ = v___x_1506_;
v_b_1488_ = v___x_1504_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1483_ = stack[0].m_obj;
lean_object* v___x_1484_ = stack[1].m_obj;
lean_object* v_as_1485_ = stack[2].m_obj;
size_t v_sz_1486_ = stack[3].m_num;
size_t v_i_1487_ = stack[4].m_num;
lean_object* v_b_1488_ = stack[5].m_obj;
lean_object* v___y_1489_ = stack[6].m_obj;
lean_object* v___y_1490_ = stack[7].m_obj;
lean_object* v___y_1491_ = stack[8].m_obj;
lean_object* v___y_1492_ = stack[9].m_obj;
lean_object* v_res_1539_;
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1483_, v___x_1484_, v_as_1485_, v_sz_1486_, v_i_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
stack->m_obj
 = v_res_1539_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1540_, lean_object* v___x_1541_, lean_object* v_as_1542_, lean_object* v_sz_1543_, lean_object* v_i_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_sz_boxed_1551_; size_t v_i_boxed_1552_; lean_object* v_res_1553_; 
v_sz_boxed_1551_ = lean_unbox_usize(v_sz_1543_);
lean_dec(v_sz_1543_);
v_i_boxed_1552_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1540_, v___x_1541_, v_as_1542_, v_sz_boxed_1551_, v_i_boxed_1552_, v_b_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_as_1542_);
lean_dec_ref(v_goal_1540_);
return v_res_1553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1554_, lean_object* v___x_1555_, lean_object* v_as_1556_, size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec_ref(v___x_1555_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_b_1559_);
return v___x_1566_;
}
else
{
lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1608_; 
v_snd_1567_ = lean_ctor_get(v_b_1559_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_b_1559_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_b_1559_, 0);
lean_dec(v_unused_1609_);
v___x_1569_ = v_b_1559_;
v_isShared_1570_ = v_isSharedCheck_1608_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_dec(v_b_1559_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1608_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v_a_1573_; lean_object* v_a_1580_; lean_object* v___x_1581_; 
v___x_1571_ = lean_box(0);
v_a_1580_ = lean_array_uget_borrowed(v_as_1556_, v_i_1558_);
lean_inc(v_a_1580_);
v___x_1581_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1554_, v_a_1580_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1582_);
if (v___x_1583_ == 0)
{
lean_dec(v_a_1582_);
v_a_1573_ = v_snd_1567_;
goto v___jp_1572_;
}
else
{
lean_object* v_type_1584_; lean_object* v___x_1585_; 
v_type_1584_ = lean_ctor_get(v___x_1555_, 2);
lean_inc(v_a_1582_);
lean_inc_ref(v_type_1584_);
v___x_1585_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1584_, v_a_1582_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = lean_unbox(v_a_1586_);
lean_dec(v_a_1586_);
if (v___x_1587_ == 0)
{
lean_dec(v_a_1582_);
v_a_1573_ = v_snd_1567_;
goto v___jp_1572_;
}
else
{
lean_object* v_self_1588_; lean_object* v___x_1589_; 
v_self_1588_ = lean_ctor_get(v_a_1582_, 0);
lean_inc_ref(v_self_1588_);
lean_dec(v_a_1582_);
v___x_1589_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1555_, v_self_1588_);
if (lean_obj_tag(v___x_1589_) == 1)
{
lean_object* v_val_1590_; lean_object* v___x_1591_; 
v_val_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1554_, v_self_1588_, v_val_1590_, v_snd_1567_);
v_a_1573_ = v___x_1591_;
goto v___jp_1572_;
}
else
{
lean_dec(v___x_1589_);
lean_dec_ref(v_self_1588_);
v_a_1573_ = v_snd_1567_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_a_1582_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec_ref(v___x_1555_);
v_a_1592_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1585_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1585_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec_ref(v___x_1555_);
v_a_1600_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1581_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1581_);
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
v___jp_1572_:
{
lean_object* v___x_1575_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_a_1573_);
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1575_ = v___x_1569_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_a_1573_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((size_t)1ULL);
v___x_1577_ = lean_usize_add(v_i_1558_, v___x_1576_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1554_, v___x_1555_, v_as_1556_, v_sz_1557_, v___x_1577_, v___x_1575_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1578_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1554_ = stack[0].m_obj;
lean_object* v___x_1555_ = stack[1].m_obj;
lean_object* v_as_1556_ = stack[2].m_obj;
size_t v_sz_1557_ = stack[3].m_num;
size_t v_i_1558_ = stack[4].m_num;
lean_object* v_b_1559_ = stack[5].m_obj;
lean_object* v___y_1560_ = stack[6].m_obj;
lean_object* v___y_1561_ = stack[7].m_obj;
lean_object* v___y_1562_ = stack[8].m_obj;
lean_object* v___y_1563_ = stack[9].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1554_, v___x_1555_, v_as_1556_, v_sz_1557_, v_i_1558_, v_b_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
stack->m_obj
 = v_res_1610_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1611_, lean_object* v___x_1612_, lean_object* v_as_1613_, lean_object* v_sz_1614_, lean_object* v_i_1615_, lean_object* v_b_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
size_t v_sz_boxed_1622_; size_t v_i_boxed_1623_; lean_object* v_res_1624_; 
v_sz_boxed_1622_ = lean_unbox_usize(v_sz_1614_);
lean_dec(v_sz_1614_);
v_i_boxed_1623_ = lean_unbox_usize(v_i_1615_);
lean_dec(v_i_1615_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1611_, v___x_1612_, v_as_1613_, v_sz_boxed_1622_, v_i_boxed_1623_, v_b_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec_ref(v_as_1613_);
lean_dec_ref(v_goal_1611_);
return v_res_1624_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1625_, lean_object* v___x_1626_, lean_object* v_t_1627_, lean_object* v_init_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_root_1634_; lean_object* v_tail_1635_; lean_object* v___x_1636_; 
v_root_1634_ = lean_ctor_get(v_t_1627_, 0);
v_tail_1635_ = lean_ctor_get(v_t_1627_, 1);
lean_inc_ref(v___x_1626_);
lean_inc_ref(v_init_1628_);
v___x_1636_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1628_, v_goal_1625_, v___x_1626_, v_root_1634_, v_init_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec_ref(v_init_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1673_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1673_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1673_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
if (lean_obj_tag(v_a_1637_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; 
lean_dec_ref(v___x_1626_);
v_a_1641_ = lean_ctor_get(v_a_1637_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v_a_1637_, 1);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_a_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; size_t v_sz_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
lean_del_object(v___x_1639_);
v_a_1645_ = lean_ctor_get(v_a_1637_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v_a_1637_, 1);
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_a_1645_);
v_sz_1648_ = lean_array_size(v_tail_1635_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1625_, v___x_1626_, v_tail_1635_, v_sz_1648_, v___x_1649_, v___x_1647_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1664_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1664_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1664_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_fst_1655_; 
v_fst_1655_ = lean_ctor_get(v_a_1651_, 0);
if (lean_obj_tag(v_fst_1655_) == 0)
{
lean_object* v_snd_1656_; lean_object* v___x_1658_; 
v_snd_1656_ = lean_ctor_get(v_a_1651_, 1);
lean_inc(v_snd_1656_);
lean_dec(v_a_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v_snd_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_snd_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v_val_1660_; lean_object* v___x_1662_; 
lean_inc_ref(v_fst_1655_);
lean_dec(v_a_1651_);
v_val_1660_ = lean_ctor_get(v_fst_1655_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v_fst_1655_, 1);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v_val_1660_);
v___x_1662_ = v___x_1653_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_val_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1650_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1650_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v___x_1626_);
v_a_1674_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1636_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1636_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1625_ = stack[0].m_obj;
lean_object* v___x_1626_ = stack[1].m_obj;
lean_object* v_t_1627_ = stack[2].m_obj;
lean_object* v_init_1628_ = stack[3].m_obj;
lean_object* v___y_1629_ = stack[4].m_obj;
lean_object* v___y_1630_ = stack[5].m_obj;
lean_object* v___y_1631_ = stack[6].m_obj;
lean_object* v___y_1632_ = stack[7].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1625_, v___x_1626_, v_t_1627_, v_init_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1683_, lean_object* v___x_1684_, lean_object* v_t_1685_, lean_object* v_init_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1683_, v___x_1684_, v_t_1685_, v_init_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec_ref(v_t_1685_);
lean_dec_ref(v_goal_1683_);
return v_res_1692_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1693_, lean_object* v_as_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_b_1697_);
return v___x_1704_;
}
else
{
lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1736_; 
v_snd_1705_ = lean_ctor_get(v_b_1697_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_b_1697_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v_b_1697_, 0);
lean_dec(v_unused_1737_);
v___x_1707_ = v_b_1697_;
v_isShared_1708_ = v_isSharedCheck_1736_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_dec(v_b_1697_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1736_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v_a_1711_; lean_object* v_a_1718_; lean_object* v___x_1719_; 
v___x_1709_ = lean_box(0);
v_a_1718_ = lean_array_uget_borrowed(v_as_1694_, v_i_1696_);
lean_inc(v_a_1718_);
v___x_1719_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1693_, v_a_1718_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v_self_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v_self_1721_ = lean_ctor_get(v_a_1720_, 0);
lean_inc_ref_n(v_self_1721_, 2);
lean_dec(v_a_1720_);
v___x_1722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1721_);
if (lean_obj_tag(v___x_1722_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1724_; 
v_val_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_val_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1705_, v_val_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1705_, v_self_1721_);
lean_dec_ref(v_self_1721_);
if (lean_obj_tag(v___x_1725_) == 1)
{
lean_object* v_val_1726_; lean_object* v___x_1727_; 
v_val_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1693_, v_val_1723_, v_val_1726_, v_snd_1705_);
v_a_1711_ = v___x_1727_;
goto v___jp_1710_;
}
else
{
lean_dec(v___x_1725_);
lean_dec(v_val_1723_);
v_a_1711_ = v_snd_1705_;
goto v___jp_1710_;
}
}
else
{
lean_dec_ref_known(v___x_1724_, 1);
lean_dec(v_val_1723_);
lean_dec_ref(v_self_1721_);
v_a_1711_ = v_snd_1705_;
goto v___jp_1710_;
}
}
else
{
lean_dec(v___x_1722_);
lean_dec_ref(v_self_1721_);
v_a_1711_ = v_snd_1705_;
goto v___jp_1710_;
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1707_);
lean_dec(v_snd_1705_);
v_a_1728_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1719_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1719_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
v___jp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_a_1711_);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1713_ = v___x_1707_;
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
v___x_1715_ = lean_usize_add(v_i_1696_, v___x_1714_);
v_i_1696_ = v___x_1715_;
v_b_1697_ = v___x_1713_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1693_ = stack[0].m_obj;
lean_object* v_as_1694_ = stack[1].m_obj;
size_t v_sz_1695_ = stack[2].m_num;
size_t v_i_1696_ = stack[3].m_num;
lean_object* v_b_1697_ = stack[4].m_obj;
lean_object* v___y_1698_ = stack[5].m_obj;
lean_object* v___y_1699_ = stack[6].m_obj;
lean_object* v___y_1700_ = stack[7].m_obj;
lean_object* v___y_1701_ = stack[8].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1693_, v_as_1694_, v_sz_1695_, v_i_1696_, v_b_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1739_, lean_object* v_as_1740_, lean_object* v_sz_1741_, lean_object* v_i_1742_, lean_object* v_b_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
size_t v_sz_boxed_1749_; size_t v_i_boxed_1750_; lean_object* v_res_1751_; 
v_sz_boxed_1749_ = lean_unbox_usize(v_sz_1741_);
lean_dec(v_sz_1741_);
v_i_boxed_1750_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1739_, v_as_1740_, v_sz_boxed_1749_, v_i_boxed_1750_, v_b_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_as_1740_);
lean_dec_ref(v_goal_1739_);
return v_res_1751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1752_, lean_object* v_as_1753_, size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_b_1756_);
return v___x_1763_;
}
else
{
lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1795_; 
v_snd_1764_ = lean_ctor_get(v_b_1756_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_b_1756_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_b_1756_, 0);
lean_dec(v_unused_1796_);
v___x_1766_ = v_b_1756_;
v_isShared_1767_ = v_isSharedCheck_1795_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_dec(v_b_1756_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1795_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v_a_1770_; lean_object* v_a_1777_; lean_object* v___x_1778_; 
v___x_1768_ = lean_box(0);
v_a_1777_ = lean_array_uget_borrowed(v_as_1753_, v_i_1755_);
lean_inc(v_a_1777_);
v___x_1778_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1752_, v_a_1777_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v_self_1780_; lean_object* v___x_1781_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v_self_1780_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref_n(v_self_1780_, 2);
lean_dec(v_a_1779_);
v___x_1781_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1780_);
if (lean_obj_tag(v___x_1781_) == 1)
{
lean_object* v_val_1782_; lean_object* v___x_1783_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1764_, v_val_1782_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1764_, v_self_1780_);
lean_dec_ref(v_self_1780_);
if (lean_obj_tag(v___x_1784_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1752_, v_val_1782_, v_val_1785_, v_snd_1764_);
v_a_1770_ = v___x_1786_;
goto v___jp_1769_;
}
else
{
lean_dec(v___x_1784_);
lean_dec(v_val_1782_);
v_a_1770_ = v_snd_1764_;
goto v___jp_1769_;
}
}
else
{
lean_dec_ref_known(v___x_1783_, 1);
lean_dec(v_val_1782_);
lean_dec_ref(v_self_1780_);
v_a_1770_ = v_snd_1764_;
goto v___jp_1769_;
}
}
else
{
lean_dec(v___x_1781_);
lean_dec_ref(v_self_1780_);
v_a_1770_ = v_snd_1764_;
goto v___jp_1769_;
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_del_object(v___x_1766_);
lean_dec(v_snd_1764_);
v_a_1787_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
v___jp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_a_1770_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1770_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_add(v_i_1755_, v___x_1773_);
v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1752_, v_as_1753_, v_sz_1754_, v___x_1774_, v___x_1772_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1775_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1752_ = stack[0].m_obj;
lean_object* v_as_1753_ = stack[1].m_obj;
size_t v_sz_1754_ = stack[2].m_num;
size_t v_i_1755_ = stack[3].m_num;
lean_object* v_b_1756_ = stack[4].m_obj;
lean_object* v___y_1757_ = stack[5].m_obj;
lean_object* v___y_1758_ = stack[6].m_obj;
lean_object* v___y_1759_ = stack[7].m_obj;
lean_object* v___y_1760_ = stack[8].m_obj;
lean_object* v_res_1797_;
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1752_, v_as_1753_, v_sz_1754_, v_i_1755_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
stack->m_obj
 = v_res_1797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1798_, lean_object* v_as_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1798_, v_as_1799_, v_sz_boxed_1808_, v_i_boxed_1809_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_as_1799_);
lean_dec_ref(v_goal_1798_);
return v_res_1810_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1811_, lean_object* v_as_1812_, size_t v_sz_1813_, size_t v_i_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_lt(v_i_1814_, v_sz_1813_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_b_1815_);
return v___x_1822_;
}
else
{
lean_object* v_snd_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1854_; 
v_snd_1823_ = lean_ctor_get(v_b_1815_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_b_1815_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_b_1815_, 0);
lean_dec(v_unused_1855_);
v___x_1825_ = v_b_1815_;
v_isShared_1826_ = v_isSharedCheck_1854_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_snd_1823_);
lean_dec(v_b_1815_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1854_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v_a_1829_; lean_object* v_a_1836_; lean_object* v___x_1837_; 
v___x_1827_ = lean_box(0);
v_a_1836_ = lean_array_uget_borrowed(v_as_1812_, v_i_1814_);
lean_inc(v_a_1836_);
v___x_1837_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1811_, v_a_1836_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v_self_1839_; lean_object* v___x_1840_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v_self_1839_ = lean_ctor_get(v_a_1838_, 0);
lean_inc_ref_n(v_self_1839_, 2);
lean_dec(v_a_1838_);
v___x_1840_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1839_);
if (lean_obj_tag(v___x_1840_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1842_; 
v_val_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_val_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1823_, v_val_1841_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1823_, v_self_1839_);
lean_dec_ref(v_self_1839_);
if (lean_obj_tag(v___x_1843_) == 1)
{
lean_object* v_val_1844_; lean_object* v___x_1845_; 
v_val_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1811_, v_val_1841_, v_val_1844_, v_snd_1823_);
v_a_1829_ = v___x_1845_;
goto v___jp_1828_;
}
else
{
lean_dec(v___x_1843_);
lean_dec(v_val_1841_);
v_a_1829_ = v_snd_1823_;
goto v___jp_1828_;
}
}
else
{
lean_dec_ref_known(v___x_1842_, 1);
lean_dec(v_val_1841_);
lean_dec_ref(v_self_1839_);
v_a_1829_ = v_snd_1823_;
goto v___jp_1828_;
}
}
else
{
lean_dec(v___x_1840_);
lean_dec_ref(v_self_1839_);
v_a_1829_ = v_snd_1823_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_del_object(v___x_1825_);
lean_dec(v_snd_1823_);
v_a_1846_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
v___jp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v_a_1829_);
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1831_ = v___x_1825_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_a_1829_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
size_t v___x_1832_; size_t v___x_1833_; 
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_add(v_i_1814_, v___x_1832_);
v_i_1814_ = v___x_1833_;
v_b_1815_ = v___x_1831_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1811_ = stack[0].m_obj;
lean_object* v_as_1812_ = stack[1].m_obj;
size_t v_sz_1813_ = stack[2].m_num;
size_t v_i_1814_ = stack[3].m_num;
lean_object* v_b_1815_ = stack[4].m_obj;
lean_object* v___y_1816_ = stack[5].m_obj;
lean_object* v___y_1817_ = stack[6].m_obj;
lean_object* v___y_1818_ = stack[7].m_obj;
lean_object* v___y_1819_ = stack[8].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1811_, v_as_1812_, v_sz_1813_, v_i_1814_, v_b_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1857_, lean_object* v_as_1858_, lean_object* v_sz_1859_, lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1859_);
lean_dec(v_sz_1859_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1857_, v_as_1858_, v_sz_boxed_1867_, v_i_boxed_1868_, v_b_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_as_1858_);
lean_dec_ref(v_goal_1857_);
return v_res_1869_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1870_, lean_object* v_as_1871_, size_t v_sz_1872_, size_t v_i_1873_, lean_object* v_b_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_usize_dec_lt(v_i_1873_, v_sz_1872_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_b_1874_);
return v___x_1881_;
}
else
{
lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1913_; 
v_snd_1882_ = lean_ctor_get(v_b_1874_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_b_1874_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v_b_1874_, 0);
lean_dec(v_unused_1914_);
v___x_1884_ = v_b_1874_;
v_isShared_1885_ = v_isSharedCheck_1913_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_dec(v_b_1874_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1913_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v_a_1888_; lean_object* v_a_1895_; lean_object* v___x_1896_; 
v___x_1886_ = lean_box(0);
v_a_1895_ = lean_array_uget_borrowed(v_as_1871_, v_i_1873_);
lean_inc(v_a_1895_);
v___x_1896_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1870_, v_a_1895_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v_self_1898_; lean_object* v___x_1899_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v_self_1898_ = lean_ctor_get(v_a_1897_, 0);
lean_inc_ref_n(v_self_1898_, 2);
lean_dec(v_a_1897_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1898_);
if (lean_obj_tag(v___x_1899_) == 1)
{
lean_object* v_val_1900_; lean_object* v___x_1901_; 
v_val_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1882_, v_val_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1882_, v_self_1898_);
lean_dec_ref(v_self_1898_);
if (lean_obj_tag(v___x_1902_) == 1)
{
lean_object* v_val_1903_; lean_object* v___x_1904_; 
v_val_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1870_, v_val_1900_, v_val_1903_, v_snd_1882_);
v_a_1888_ = v___x_1904_;
goto v___jp_1887_;
}
else
{
lean_dec(v___x_1902_);
lean_dec(v_val_1900_);
v_a_1888_ = v_snd_1882_;
goto v___jp_1887_;
}
}
else
{
lean_dec_ref_known(v___x_1901_, 1);
lean_dec(v_val_1900_);
lean_dec_ref(v_self_1898_);
v_a_1888_ = v_snd_1882_;
goto v___jp_1887_;
}
}
else
{
lean_dec(v___x_1899_);
lean_dec_ref(v_self_1898_);
v_a_1888_ = v_snd_1882_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_del_object(v___x_1884_);
lean_dec(v_snd_1882_);
v_a_1905_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1896_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1896_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
v___jp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v_a_1888_);
lean_ctor_set(v___x_1884_, 0, v___x_1886_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1888_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1873_, v___x_1891_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1870_, v_as_1871_, v_sz_1872_, v___x_1892_, v___x_1890_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1870_ = stack[0].m_obj;
lean_object* v_as_1871_ = stack[1].m_obj;
size_t v_sz_1872_ = stack[2].m_num;
size_t v_i_1873_ = stack[3].m_num;
lean_object* v_b_1874_ = stack[4].m_obj;
lean_object* v___y_1875_ = stack[5].m_obj;
lean_object* v___y_1876_ = stack[6].m_obj;
lean_object* v___y_1877_ = stack[7].m_obj;
lean_object* v___y_1878_ = stack[8].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1870_, v_as_1871_, v_sz_1872_, v_i_1873_, v_b_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1916_, lean_object* v_as_1917_, lean_object* v_sz_1918_, lean_object* v_i_1919_, lean_object* v_b_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
size_t v_sz_boxed_1926_; size_t v_i_boxed_1927_; lean_object* v_res_1928_; 
v_sz_boxed_1926_ = lean_unbox_usize(v_sz_1918_);
lean_dec(v_sz_1918_);
v_i_boxed_1927_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1916_, v_as_1917_, v_sz_boxed_1926_, v_i_boxed_1927_, v_b_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v_as_1917_);
lean_dec_ref(v_goal_1916_);
return v_res_1928_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1929_, lean_object* v_goal_1930_, lean_object* v_n_1931_, lean_object* v_b_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
if (lean_obj_tag(v_n_1931_) == 0)
{
lean_object* v_cs_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v_cs_1938_ = lean_ctor_get(v_n_1931_, 0);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_b_1932_);
v_sz_1941_ = lean_array_size(v_cs_1938_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1929_, v_goal_1930_, v_cs_1938_, v_sz_1941_, v___x_1942_, v___x_1940_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1958_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1958_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1958_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_fst_1948_; 
v_fst_1948_ = lean_ctor_get(v_a_1944_, 0);
if (lean_obj_tag(v_fst_1948_) == 0)
{
lean_object* v_snd_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_snd_1949_ = lean_ctor_get(v_a_1944_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1944_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_snd_1949_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1950_);
v___x_1952_ = v___x_1946_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
else
{
lean_object* v_val_1954_; lean_object* v___x_1956_; 
lean_inc_ref(v_fst_1948_);
lean_dec(v_a_1944_);
v_val_1954_ = lean_ctor_get(v_fst_1948_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v_fst_1948_, 1);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_val_1954_);
v___x_1956_ = v___x_1946_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_val_1954_);
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
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1943_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1943_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_vs_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; size_t v_sz_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v_vs_1967_ = lean_ctor_get(v_n_1931_, 0);
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v_b_1932_);
v_sz_1970_ = lean_array_size(v_vs_1967_);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1930_, v_vs_1967_, v_sz_1970_, v___x_1971_, v___x_1969_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1987_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_fst_1977_; 
v_fst_1977_ = lean_ctor_get(v_a_1973_, 0);
if (lean_obj_tag(v_fst_1977_) == 0)
{
lean_object* v_snd_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v_snd_1978_ = lean_ctor_get(v_a_1973_, 1);
lean_inc(v_snd_1978_);
lean_dec(v_a_1973_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_snd_1978_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; 
lean_inc_ref(v_fst_1977_);
lean_dec(v_a_1973_);
v_val_1983_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v_fst_1977_, 1);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_val_1983_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_val_1983_);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1972_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1972_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1929_ = stack[0].m_obj;
lean_object* v_goal_1930_ = stack[1].m_obj;
lean_object* v_n_1931_ = stack[2].m_obj;
lean_object* v_b_1932_ = stack[3].m_obj;
lean_object* v___y_1933_ = stack[4].m_obj;
lean_object* v___y_1934_ = stack[5].m_obj;
lean_object* v___y_1935_ = stack[6].m_obj;
lean_object* v___y_1936_ = stack[7].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1929_, v_goal_1930_, v_n_1931_, v_b_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
stack->m_obj
 = v_res_1996_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1997_, lean_object* v_goal_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_b_2002_);
return v___x_2009_;
}
else
{
lean_object* v_snd_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2044_; 
v_snd_2010_ = lean_ctor_get(v_b_2002_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_b_2002_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v_b_2002_, 0);
lean_dec(v_unused_2045_);
v___x_2012_ = v_b_2002_;
v_isShared_2013_ = v_isSharedCheck_2044_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2010_);
lean_dec(v_b_2002_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2044_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v_a_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
v_a_2015_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
lean_inc(v_snd_2010_);
v___x_2016_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1997_, v_goal_1998_, v_a_2015_, v_snd_2010_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2035_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2035_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2035_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
if (lean_obj_tag(v_a_2017_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2017_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2021_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_snd_2010_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; 
lean_del_object(v___x_2019_);
lean_dec(v_snd_2010_);
v_a_2028_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v_a_2017_, 1);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_a_2028_);
lean_ctor_set(v___x_2012_, 0, v___x_2014_);
v___x_2030_ = v___x_2012_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_a_2028_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
size_t v___x_2031_; size_t v___x_2032_; 
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2001_, v___x_2031_);
v_i_2001_ = v___x_2032_;
v_b_2002_ = v___x_2030_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_2012_);
lean_dec(v_snd_2010_);
v_a_2036_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2016_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2016_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1997_ = stack[0].m_obj;
lean_object* v_goal_1998_ = stack[1].m_obj;
lean_object* v_as_1999_ = stack[2].m_obj;
size_t v_sz_2000_ = stack[3].m_num;
size_t v_i_2001_ = stack[4].m_num;
lean_object* v_b_2002_ = stack[5].m_obj;
lean_object* v___y_2003_ = stack[6].m_obj;
lean_object* v___y_2004_ = stack[7].m_obj;
lean_object* v___y_2005_ = stack[8].m_obj;
lean_object* v___y_2006_ = stack[9].m_obj;
lean_object* v_res_2046_;
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1997_, v_goal_1998_, v_as_1999_, v_sz_2000_, v_i_2001_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2047_, lean_object* v_goal_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2047_, v_goal_2048_, v_as_2049_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
lean_dec_ref(v_goal_2048_);
lean_dec_ref(v_init_2047_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2061_, lean_object* v_goal_2062_, lean_object* v_n_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2061_, v_goal_2062_, v_n_2063_, v_b_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_n_2063_);
lean_dec_ref(v_goal_2062_);
lean_dec_ref(v_init_2061_);
return v_res_2070_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2071_, lean_object* v_t_2072_, lean_object* v_init_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_root_2079_; lean_object* v_tail_2080_; lean_object* v___x_2081_; 
v_root_2079_ = lean_ctor_get(v_t_2072_, 0);
v_tail_2080_ = lean_ctor_get(v_t_2072_, 1);
lean_inc_ref(v_init_2073_);
v___x_2081_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2073_, v_goal_2071_, v_root_2079_, v_init_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec_ref(v_init_2073_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2118_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
if (lean_obj_tag(v_a_2082_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v_a_2082_, 1);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v_a_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
lean_del_object(v___x_2084_);
v_a_2090_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v_a_2082_, 1);
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_a_2090_);
v_sz_2093_ = lean_array_size(v_tail_2080_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2071_, v_tail_2080_, v_sz_2093_, v___x_2094_, v___x_2092_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2109_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; 
v_fst_2100_ = lean_ctor_get(v_a_2096_, 0);
if (lean_obj_tag(v_fst_2100_) == 0)
{
lean_object* v_snd_2101_; lean_object* v___x_2103_; 
v_snd_2101_ = lean_ctor_get(v_a_2096_, 1);
lean_inc(v_snd_2101_);
lean_dec(v_a_2096_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_snd_2101_);
v___x_2103_ = v___x_2098_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_snd_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
else
{
lean_object* v_val_2105_; lean_object* v___x_2107_; 
lean_inc_ref(v_fst_2100_);
lean_dec(v_a_2096_);
v_val_2105_ = lean_ctor_get(v_fst_2100_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_fst_2100_, 1);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_val_2105_);
v___x_2107_ = v___x_2098_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_val_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_a_2110_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2095_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2095_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_a_2119_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2081_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2081_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2071_ = stack[0].m_obj;
lean_object* v_t_2072_ = stack[1].m_obj;
lean_object* v_init_2073_ = stack[2].m_obj;
lean_object* v___y_2074_ = stack[3].m_obj;
lean_object* v___y_2075_ = stack[4].m_obj;
lean_object* v___y_2076_ = stack[5].m_obj;
lean_object* v___y_2077_ = stack[6].m_obj;
lean_object* v_res_2127_;
v_res_2127_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2071_, v_t_2072_, v_init_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
stack->m_obj
 = v_res_2127_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2128_, lean_object* v_t_2129_, lean_object* v_init_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2128_, v_t_2129_, v_init_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_t_2129_);
lean_dec_ref(v_goal_2128_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_unsigned_to_nat(16u);
v___x_2139_ = lean_mk_array(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_model_2142_; 
v___x_2140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2141_ = lean_unsigned_to_nat(0u);
v_model_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2142_, 0, v___x_2141_);
lean_ctor_set(v_model_2142_, 1, v___x_2140_);
return v_model_2142_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2150_, lean_object* v_structId_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_ref_2157_; lean_object* v___x_2158_; lean_object* v_model_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_ref_2157_ = lean_ctor_get(v_a_2154_, 2);
v___x_2158_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2159_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2160_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2161_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2160_, v_goal_2150_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v_toGoalState_2163_; lean_object* v_structs_2164_; lean_object* v_exprs_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v_toGoalState_2163_ = lean_ctor_get(v_goal_2150_, 0);
v_structs_2164_ = lean_ctor_get(v_a_2162_, 0);
lean_inc_ref(v_structs_2164_);
lean_dec(v_a_2162_);
v_exprs_2165_ = lean_ctor_get(v_toGoalState_2163_, 2);
v___x_2166_ = lean_array_get(v___x_2158_, v_structs_2164_, v_structId_2151_);
lean_dec_ref(v_structs_2164_);
lean_inc(v___x_2166_);
v___x_2167_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2150_, v___x_2166_, v_exprs_2165_, v_model_2159_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2150_, v_structId_2151_, v_a_2168_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2150_, v_exprs_2165_, v_a_2170_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_type_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v_type_2173_ = lean_ctor_get(v___x_2166_, 2);
lean_inc_ref(v_type_2173_);
lean_dec(v___x_2166_);
v___x_2174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2174_, 0, v_type_2173_);
v___x_2175_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2150_, v___x_2174_, v_a_2172_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2178_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2177_, v_a_2176_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2186_);
v___x_2180_ = v___x_2178_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v___x_2178_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v_a_2176_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2176_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2176_);
v_a_2187_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2178_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
return v___x_2175_;
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v___x_2166_);
v_a_2195_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2171_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2171_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v___x_2166_);
v_a_2203_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2169_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2169_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v___x_2166_);
v_a_2211_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2167_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2167_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
v_a_2219_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2221_ = v___x_2161_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2161_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2223_ = lean_io_error_to_string(v_a_2219_);
v___x_2224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_ofFormat(v___x_2224_);
lean_inc(v_ref_2157_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_ref_2157_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2226_);
v___x_2228_ = v___x_2221_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_mkModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2150_ = stack[0].m_obj;
lean_object* v_structId_2151_ = stack[1].m_obj;
lean_object* v_a_2152_ = stack[2].m_obj;
lean_object* v_a_2153_ = stack[3].m_obj;
lean_object* v_a_2154_ = stack[4].m_obj;
lean_object* v_a_2155_ = stack[5].m_obj;
lean_object* v_res_2231_;
v_res_2231_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2150_, v_structId_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
stack->m_obj
 = v_res_2231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2232_, lean_object* v_structId_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2232_, v_structId_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_structId_2233_);
lean_dec_ref(v_goal_2232_);
return v_res_2239_;
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

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
lean_object* v_arg_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_arg_212_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_arg_212_);
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_214_ = l_Lean_Expr_isApp(v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v___x_213_);
lean_dec_ref(v_arg_212_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_213_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_212_);
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_221_ = l_Lean_Expr_isConstOf(v___x_219_, v___x_220_);
lean_dec_ref(v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v_arg_212_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_arg_212_);
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Rat_ofInt(v_a_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_nat_to_int(v_a_226_);
v___x_228_ = l_Rat_ofInt(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v_tail_234_; uint8_t v___x_235_; 
v_key_232_ = lean_ctor_get(v_x_230_, 0);
v_value_233_ = lean_ctor_get(v_x_230_, 1);
v_tail_234_ = lean_ctor_get(v_x_230_, 2);
v___x_235_ = lean_expr_eqv(v_key_232_, v_a_229_);
if (v___x_235_ == 0)
{
v_x_230_ = v_tail_234_;
goto _start;
}
else
{
lean_object* v___x_237_; 
lean_inc(v_value_233_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_value_233_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_238_, v_x_239_);
lean_dec(v_x_239_);
lean_dec_ref(v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_buckets_243_; lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_buckets_243_ = lean_ctor_get(v_m_241_, 1);
v___x_244_ = lean_array_get_size(v_buckets_243_);
v___x_245_ = l_Lean_Expr_hash(v_a_242_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_244_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v___x_257_ = lean_array_uget_borrowed(v_buckets_243_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_242_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_259_, v_a_260_);
lean_dec_ref(v_a_260_);
lean_dec_ref(v_m_259_);
return v_res_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_301_, lean_object* v_model_302_, lean_object* v_e_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_302_, v_e_303_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v___x_310_; 
lean_dec_ref(v_e_303_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
lean_dec(v___x_309_);
v___x_311_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_303_, v_a_305_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_565_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_565_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_565_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_565_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_cleanupAnnotations(v_a_312_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_321_);
goto v___jp_316_;
}
else
{
lean_object* v_arg_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_arg_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_323_);
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
lean_object* v_arg_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_arg_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc_ref(v_arg_326_);
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; 
v___x_330_ = l_Lean_Expr_isApp(v___x_327_);
if (v___x_330_ == 0)
{
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
lean_object* v_arg_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_arg_331_ = lean_ctor_get(v___x_327_, 1);
lean_inc_ref(v_arg_331_);
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_332_, v___x_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
v___x_337_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_337_ == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
v___x_339_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
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
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
goto v___jp_316_;
}
else
{
uint8_t v___x_351_; 
lean_del_object(v___x_314_);
v___x_351_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_301_, v_arg_331_);
lean_dec_ref(v_arg_331_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
if (lean_obj_tag(v_a_355_) == 0)
{
lean_dec_ref(v_arg_323_);
return v___x_354_;
}
else
{
lean_object* v_val_356_; lean_object* v___x_357_; 
lean_dec_ref_known(v___x_354_, 1);
v_val_356_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_val_356_);
lean_dec_ref_known(v_a_355_, 1);
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
if (lean_obj_tag(v_a_358_) == 0)
{
lean_dec(v_val_356_);
return v___x_357_;
}
else
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_374_; 
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_375_);
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
else
{
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_val_362_ = lean_ctor_get(v_a_358_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_373_ == 0)
{
v___x_364_ = v_a_358_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v_a_358_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = l_Rat_add(v_val_356_, v_val_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_368_);
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
else
{
lean_dec(v_val_356_);
return v___x_357_;
}
}
}
else
{
lean_dec_ref(v_arg_323_);
return v___x_354_;
}
}
}
}
else
{
uint8_t v___x_376_; 
lean_dec_ref(v___x_342_);
lean_del_object(v___x_314_);
v___x_376_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_301_, v_arg_331_);
lean_dec_ref(v_arg_331_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
if (lean_obj_tag(v_a_380_) == 0)
{
lean_dec_ref(v_arg_323_);
return v___x_379_;
}
else
{
lean_object* v_val_381_; lean_object* v___x_382_; 
lean_dec_ref_known(v___x_379_, 1);
v_val_381_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v_a_380_, 1);
v___x_382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
if (lean_obj_tag(v_a_383_) == 0)
{
lean_dec(v_val_381_);
return v___x_382_;
}
else
{
lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_382_, 0);
lean_dec(v_unused_400_);
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_399_;
goto v_resetjp_384_;
}
else
{
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_399_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_val_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_398_; 
v_val_387_ = lean_ctor_get(v_a_383_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_398_ == 0)
{
v___x_389_ = v_a_383_;
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_val_387_);
lean_dec(v_a_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_398_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = l_Rat_sub(v_val_381_, v_val_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_393_);
v___x_395_ = v___x_385_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
else
{
lean_dec(v_val_381_);
return v___x_382_;
}
}
}
else
{
lean_dec_ref(v_arg_323_);
return v___x_379_;
}
}
}
}
else
{
uint8_t v___x_401_; 
lean_dec_ref(v___x_342_);
lean_del_object(v___x_314_);
v___x_401_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_301_, v_arg_331_);
lean_dec_ref(v_arg_331_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
if (lean_obj_tag(v_a_405_) == 0)
{
lean_dec_ref(v_arg_323_);
return v___x_404_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
lean_dec_ref_known(v___x_404_, 1);
v_val_406_ = lean_ctor_get(v_a_405_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_a_405_, 1);
v___x_407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
if (lean_obj_tag(v_a_408_) == 0)
{
lean_dec(v_val_406_);
return v___x_407_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_407_, 0);
lean_dec(v_unused_425_);
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
else
{
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
v_val_412_ = lean_ctor_get(v_a_408_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_423_ == 0)
{
v___x_414_ = v_a_408_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v_a_408_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = l_Rat_mul(v_val_406_, v_val_412_);
lean_dec(v_val_406_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_418_);
v___x_420_ = v___x_410_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
else
{
lean_dec(v_val_406_);
return v___x_407_;
}
}
}
else
{
lean_dec_ref(v_arg_323_);
return v___x_404_;
}
}
}
}
else
{
uint8_t v___x_426_; 
lean_dec_ref(v___x_342_);
lean_del_object(v___x_314_);
v___x_426_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_301_, v_arg_331_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; 
v___x_427_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_301_, v_arg_331_);
lean_dec_ref(v_arg_331_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_323_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_getNatValue_x3f(v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec_ref(v_arg_326_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_460_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_460_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_460_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_460_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_dec_ref(v_arg_323_);
v___x_435_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; 
lean_del_object(v___x_433_);
v_val_439_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_a_431_, 1);
v___x_440_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
if (lean_obj_tag(v_a_441_) == 0)
{
lean_dec(v_val_439_);
return v___x_440_;
}
else
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_458_; 
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_440_, 0);
lean_dec(v_unused_459_);
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_458_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_458_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_val_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_457_; 
v_val_445_ = lean_ctor_get(v_a_441_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_457_ == 0)
{
v___x_447_ = v_a_441_;
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_val_445_);
lean_dec(v_a_441_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_439_);
v___x_450_ = l_Rat_mul(v___x_449_, v_val_445_);
lean_dec_ref(v___x_449_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
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
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_452_);
v___x_454_ = v___x_443_;
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
lean_dec(v_val_439_);
return v___x_440_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_arg_323_);
v_a_461_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_430_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_430_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec_ref(v_arg_331_);
v___x_469_ = l_Lean_Meta_getIntValue_x3f(v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_499_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_499_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_499_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_499_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
if (lean_obj_tag(v_a_470_) == 0)
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_dec_ref(v_arg_323_);
v___x_474_ = lean_box(0);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v_val_478_; lean_object* v___x_479_; 
lean_del_object(v___x_472_);
v_val_478_ = lean_ctor_get(v_a_470_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v_a_470_, 1);
v___x_479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
if (lean_obj_tag(v_a_480_) == 0)
{
lean_dec(v_val_478_);
return v___x_479_;
}
else
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_498_);
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_497_;
goto v_resetjp_481_;
}
else
{
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_497_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_val_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_496_; 
v_val_484_ = lean_ctor_get(v_a_480_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_496_ == 0)
{
v___x_486_ = v_a_480_;
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_val_484_);
lean_dec(v_a_480_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = l_Rat_ofInt(v_val_478_);
v___x_489_ = l_Rat_mul(v___x_488_, v_val_484_);
lean_dec_ref(v___x_488_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_489_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_491_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
else
{
lean_dec(v_val_478_);
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_arg_323_);
v_a_500_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_469_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_469_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
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
uint8_t v___x_508_; 
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_314_);
v___x_508_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_301_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v_arg_323_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_301_, v_model_302_, v_arg_323_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
if (lean_obj_tag(v_a_512_) == 0)
{
return v___x_511_;
}
else
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_528_; 
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_511_, 0);
lean_dec(v_unused_529_);
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_528_;
goto v_resetjp_513_;
}
else
{
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_528_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_val_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_527_; 
v_val_516_ = lean_ctor_get(v_a_512_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_a_512_);
if (v_isSharedCheck_527_ == 0)
{
v___x_518_ = v_a_512_;
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_val_516_);
lean_dec(v_a_512_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Rat_neg(v_val_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_524_ = v___x_514_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
else
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v___x_530_; 
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_arg_323_);
lean_del_object(v___x_314_);
v___x_530_ = l_Lean_Meta_getNatValue_x3f(v_arg_326_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec_ref(v_arg_326_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_551_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_551_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_551_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_551_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_box(0);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
v_val_539_ = lean_ctor_get(v_a_531_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_550_ == 0)
{
v___x_541_ = v_a_531_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v_a_531_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_545_);
v___x_547_ = v___x_533_;
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
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_530_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_530_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
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
uint8_t v___x_560_; 
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_del_object(v___x_314_);
v___x_560_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_301_, v_arg_323_);
lean_dec_ref(v_arg_323_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_box(0);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_a_566_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_311_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_311_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_574_, lean_object* v_model_575_, lean_object* v_e_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_574_, v_model_575_, v_e_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec_ref(v_model_575_);
lean_dec_ref(v_s_574_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_583_, lean_object* v_m_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_584_, v_a_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_587_, lean_object* v_m_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_587_, v_m_588_, v_a_589_);
lean_dec_ref(v_a_589_);
lean_dec_ref(v_m_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_nat_to_int(v_a_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_593_, lean_object* v_a_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_597_, lean_object* v_a_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_597_, v_a_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_a_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_601_, lean_object* v_s_602_, lean_object* v_model_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_602_, v_model_603_, v_e_601_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_610_, lean_object* v_s_611_, lean_object* v_model_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_610_, v_s_611_, v_model_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_model_612_);
lean_dec_ref(v_s_611_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
else
{
lean_object* v_key_622_; lean_object* v_tail_623_; uint8_t v___x_624_; 
v_key_622_ = lean_ctor_get(v_x_620_, 0);
v_tail_623_ = lean_ctor_get(v_x_620_, 2);
v___x_624_ = lean_expr_eqv(v_key_622_, v_a_619_);
if (v___x_624_ == 0)
{
v_x_620_ = v_tail_623_;
goto _start;
}
else
{
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_626_, v_x_627_);
lean_dec(v_x_627_);
lean_dec_ref(v_a_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_buckets_632_; lean_object* v___x_633_; uint64_t v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v_fold_637_; uint64_t v___x_638_; uint64_t v___x_639_; uint64_t v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_buckets_632_ = lean_ctor_get(v_m_630_, 1);
v___x_633_ = lean_array_get_size(v_buckets_632_);
v___x_634_ = l_Lean_Expr_hash(v_a_631_);
v___x_635_ = 32ULL;
v___x_636_ = lean_uint64_shift_right(v___x_634_, v___x_635_);
v_fold_637_ = lean_uint64_xor(v___x_634_, v___x_636_);
v___x_638_ = 16ULL;
v___x_639_ = lean_uint64_shift_right(v_fold_637_, v___x_638_);
v___x_640_ = lean_uint64_xor(v_fold_637_, v___x_639_);
v___x_641_ = lean_uint64_to_usize(v___x_640_);
v___x_642_ = lean_usize_of_nat(v___x_633_);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_sub(v___x_642_, v___x_643_);
v___x_645_ = lean_usize_land(v___x_641_, v___x_644_);
v___x_646_ = lean_array_uget_borrowed(v_buckets_632_, v___x_645_);
v___x_647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_631_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_648_, v_a_649_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_m_648_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v_structId_652_, lean_object* v___x_653_, lean_object* v_goal_654_, lean_object* v_as_655_, size_t v_sz_656_, size_t v_i_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_657_, v_sz_656_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_b_658_);
return v___x_665_;
}
else
{
lean_object* v_snd_666_; lean_object* v_a_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_696_; 
v_snd_666_ = lean_ctor_get(v_b_658_, 1);
lean_inc(v_snd_666_);
lean_dec_ref(v_b_658_);
v_a_667_ = lean_array_uget(v_as_655_, v_i_657_);
v_fst_668_ = lean_ctor_get(v_a_667_, 0);
v_snd_669_ = lean_ctor_get(v_a_667_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_696_ == 0)
{
v___x_671_ = v_a_667_;
v_isShared_672_ = v_isSharedCheck_696_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_a_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_696_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_a_675_; uint8_t v___x_682_; 
v___x_673_ = lean_box(0);
v___x_682_ = lean_nat_dec_eq(v_structId_652_, v_snd_669_);
lean_dec(v_snd_669_);
if (v___x_682_ == 0)
{
lean_dec(v_fst_668_);
v_a_675_ = v_snd_666_;
goto v___jp_674_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_666_, v_fst_668_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_fst_668_);
v___x_684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_653_, v_snd_666_, v_fst_668_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v_a_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v_a_685_, 1);
v___x_687_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_654_, v_fst_668_, v_val_686_, v_snd_666_);
v_a_675_ = v___x_687_;
goto v___jp_674_;
}
else
{
lean_dec(v_a_685_);
lean_dec(v_fst_668_);
v_a_675_ = v_snd_666_;
goto v___jp_674_;
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_671_);
lean_dec(v_fst_668_);
lean_dec(v_snd_666_);
v_a_688_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_684_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_dec(v_fst_668_);
v_a_675_ = v_snd_666_;
goto v___jp_674_;
}
}
v___jp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v_a_675_);
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_677_ = v___x_671_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_a_675_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_657_, v___x_678_);
v_i_657_ = v___x_679_;
v_b_658_ = v___x_677_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_structId_697_, lean_object* v___x_698_, lean_object* v_goal_699_, lean_object* v_as_700_, lean_object* v_sz_701_, lean_object* v_i_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_701_);
lean_dec(v_sz_701_);
v_i_boxed_710_ = lean_unbox_usize(v_i_702_);
lean_dec(v_i_702_);
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_697_, v___x_698_, v_goal_699_, v_as_700_, v_sz_boxed_709_, v_i_boxed_710_, v_b_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec_ref(v_as_700_);
lean_dec_ref(v_goal_699_);
lean_dec_ref(v___x_698_);
lean_dec(v_structId_697_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v_structId_712_, lean_object* v___x_713_, lean_object* v_goal_714_, lean_object* v_as_715_, size_t v_sz_716_, size_t v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_717_, v_sz_716_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_718_);
return v___x_725_;
}
else
{
lean_object* v_snd_726_; lean_object* v_a_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_756_; 
v_snd_726_ = lean_ctor_get(v_b_718_, 1);
lean_inc(v_snd_726_);
lean_dec_ref(v_b_718_);
v_a_727_ = lean_array_uget(v_as_715_, v_i_717_);
v_fst_728_ = lean_ctor_get(v_a_727_, 0);
v_snd_729_ = lean_ctor_get(v_a_727_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_756_ == 0)
{
v___x_731_ = v_a_727_;
v_isShared_732_ = v_isSharedCheck_756_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v_a_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_756_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_a_735_; uint8_t v___x_742_; 
v___x_733_ = lean_box(0);
v___x_742_ = lean_nat_dec_eq(v_structId_712_, v_snd_729_);
lean_dec(v_snd_729_);
if (v___x_742_ == 0)
{
lean_dec(v_fst_728_);
v_a_735_ = v_snd_726_;
goto v___jp_734_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_726_, v_fst_728_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_inc(v_fst_728_);
v___x_744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_713_, v_snd_726_, v_fst_728_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
if (lean_obj_tag(v_a_745_) == 1)
{
lean_object* v_val_746_; lean_object* v___x_747_; 
v_val_746_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_a_745_, 1);
v___x_747_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_714_, v_fst_728_, v_val_746_, v_snd_726_);
v_a_735_ = v___x_747_;
goto v___jp_734_;
}
else
{
lean_dec(v_a_745_);
lean_dec(v_fst_728_);
v_a_735_ = v_snd_726_;
goto v___jp_734_;
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_del_object(v___x_731_);
lean_dec(v_fst_728_);
lean_dec(v_snd_726_);
v_a_748_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_744_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_dec(v_fst_728_);
v_a_735_ = v_snd_726_;
goto v___jp_734_;
}
}
v___jp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_a_735_);
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_737_ = v___x_731_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_a_735_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_add(v_i_717_, v___x_738_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_712_, v___x_713_, v_goal_714_, v_as_715_, v_sz_716_, v___x_739_, v___x_737_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v_structId_757_, lean_object* v___x_758_, lean_object* v_goal_759_, lean_object* v_as_760_, lean_object* v_sz_761_, lean_object* v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_761_);
lean_dec(v_sz_761_);
v_i_boxed_770_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_757_, v___x_758_, v_goal_759_, v_as_760_, v_sz_boxed_769_, v_i_boxed_770_, v_b_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_as_760_);
lean_dec_ref(v_goal_759_);
lean_dec_ref(v___x_758_);
lean_dec(v_structId_757_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_772_, lean_object* v_structId_773_, lean_object* v___x_774_, lean_object* v_goal_775_, lean_object* v_n_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
if (lean_obj_tag(v_n_776_) == 0)
{
lean_object* v_cs_783_; lean_object* v___x_784_; lean_object* v___x_785_; size_t v_sz_786_; size_t v___x_787_; lean_object* v___x_788_; 
v_cs_783_ = lean_ctor_get(v_n_776_, 0);
v___x_784_ = lean_box(0);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_b_777_);
v_sz_786_ = lean_array_size(v_cs_783_);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_772_, v_structId_773_, v___x_774_, v_goal_775_, v_cs_783_, v_sz_786_, v___x_787_, v___x_785_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_803_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_803_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_803_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_803_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
if (lean_obj_tag(v_fst_793_) == 0)
{
lean_object* v_snd_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v_snd_794_ = lean_ctor_get(v_a_789_, 1);
lean_inc(v_snd_794_);
lean_dec(v_a_789_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v_snd_794_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_795_);
v___x_797_ = v___x_791_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; 
lean_inc_ref(v_fst_793_);
lean_dec(v_a_789_);
v_val_799_ = lean_ctor_get(v_fst_793_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v_fst_793_, 1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_val_799_);
v___x_801_ = v___x_791_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_val_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_788_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_788_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_vs_812_; lean_object* v___x_813_; lean_object* v___x_814_; size_t v_sz_815_; size_t v___x_816_; lean_object* v___x_817_; 
v_vs_812_ = lean_ctor_get(v_n_776_, 0);
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_b_777_);
v_sz_815_ = lean_array_size(v_vs_812_);
v___x_816_ = ((size_t)0ULL);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_773_, v___x_774_, v_goal_775_, v_vs_812_, v_sz_815_, v___x_816_, v___x_814_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_832_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_832_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_832_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_fst_822_; 
v_fst_822_ = lean_ctor_get(v_a_818_, 0);
if (lean_obj_tag(v_fst_822_) == 0)
{
lean_object* v_snd_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v_snd_823_ = lean_ctor_get(v_a_818_, 1);
lean_inc(v_snd_823_);
lean_dec(v_a_818_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_snd_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v_val_828_; lean_object* v___x_830_; 
lean_inc_ref(v_fst_822_);
lean_dec(v_a_818_);
v_val_828_ = lean_ctor_get(v_fst_822_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v_fst_822_, 1);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_val_828_);
v___x_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_val_828_);
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
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_817_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_817_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_841_, lean_object* v_structId_842_, lean_object* v___x_843_, lean_object* v_goal_844_, lean_object* v_as_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_848_);
return v___x_855_;
}
else
{
lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_890_; 
v_snd_856_ = lean_ctor_get(v_b_848_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v_b_848_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v_b_848_, 0);
lean_dec(v_unused_891_);
v___x_858_ = v_b_848_;
v_isShared_859_ = v_isSharedCheck_890_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_dec(v_b_848_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_890_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_array_uget_borrowed(v_as_845_, v_i_847_);
lean_inc(v_snd_856_);
v___x_861_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_841_, v_structId_842_, v___x_843_, v_goal_844_, v_a_860_, v_snd_856_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_881_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_881_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
if (lean_obj_tag(v_a_862_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_a_862_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_866_);
v___x_868_ = v___x_858_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_856_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_868_);
v___x_870_ = v___x_864_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
lean_del_object(v___x_864_);
lean_dec(v_snd_856_);
v_a_873_ = lean_ctor_get(v_a_862_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v_a_862_, 1);
v___x_874_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_a_873_);
lean_ctor_set(v___x_858_, 0, v___x_874_);
v___x_876_ = v___x_858_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_a_873_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
size_t v___x_877_; size_t v___x_878_; 
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_add(v_i_847_, v___x_877_);
v_i_847_ = v___x_878_;
v_b_848_ = v___x_876_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_858_);
lean_dec(v_snd_856_);
v_a_882_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_861_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_861_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_892_, lean_object* v_structId_893_, lean_object* v___x_894_, lean_object* v_goal_895_, lean_object* v_as_896_, lean_object* v_sz_897_, lean_object* v_i_898_, lean_object* v_b_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
size_t v_sz_boxed_905_; size_t v_i_boxed_906_; lean_object* v_res_907_; 
v_sz_boxed_905_ = lean_unbox_usize(v_sz_897_);
lean_dec(v_sz_897_);
v_i_boxed_906_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_892_, v_structId_893_, v___x_894_, v_goal_895_, v_as_896_, v_sz_boxed_905_, v_i_boxed_906_, v_b_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_as_896_);
lean_dec_ref(v_goal_895_);
lean_dec_ref(v___x_894_);
lean_dec(v_structId_893_);
lean_dec_ref(v_init_892_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_908_, lean_object* v_structId_909_, lean_object* v___x_910_, lean_object* v_goal_911_, lean_object* v_n_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_908_, v_structId_909_, v___x_910_, v_goal_911_, v_n_912_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_n_912_);
lean_dec_ref(v_goal_911_);
lean_dec_ref(v___x_910_);
lean_dec(v_structId_909_);
lean_dec_ref(v_init_908_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v_structId_920_, lean_object* v___x_921_, lean_object* v_goal_922_, lean_object* v_as_923_, size_t v_sz_924_, size_t v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = lean_usize_dec_lt(v_i_925_, v_sz_924_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_b_926_);
return v___x_933_;
}
else
{
lean_object* v_snd_934_; lean_object* v_a_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_964_; 
v_snd_934_ = lean_ctor_get(v_b_926_, 1);
lean_inc(v_snd_934_);
lean_dec_ref(v_b_926_);
v_a_935_ = lean_array_uget(v_as_923_, v_i_925_);
v_fst_936_ = lean_ctor_get(v_a_935_, 0);
v_snd_937_ = lean_ctor_get(v_a_935_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_964_ == 0)
{
v___x_939_ = v_a_935_;
v_isShared_940_ = v_isSharedCheck_964_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v_a_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_964_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v_a_943_; uint8_t v___x_950_; 
v___x_941_ = lean_box(0);
v___x_950_ = lean_nat_dec_eq(v_structId_920_, v_snd_937_);
lean_dec(v_snd_937_);
if (v___x_950_ == 0)
{
lean_dec(v_fst_936_);
v_a_943_ = v_snd_934_;
goto v___jp_942_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_934_, v_fst_936_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_inc(v_fst_936_);
v___x_952_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_921_, v_snd_934_, v_fst_936_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
if (lean_obj_tag(v_a_953_) == 1)
{
lean_object* v_val_954_; lean_object* v___x_955_; 
v_val_954_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v_a_953_, 1);
v___x_955_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_922_, v_fst_936_, v_val_954_, v_snd_934_);
v_a_943_ = v___x_955_;
goto v___jp_942_;
}
else
{
lean_dec(v_a_953_);
lean_dec(v_fst_936_);
v_a_943_ = v_snd_934_;
goto v___jp_942_;
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_939_);
lean_dec(v_fst_936_);
lean_dec(v_snd_934_);
v_a_956_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_952_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_dec(v_fst_936_);
v_a_943_ = v_snd_934_;
goto v___jp_942_;
}
}
v___jp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v_a_943_);
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_943_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_925_, v___x_946_);
v_i_925_ = v___x_947_;
v_b_926_ = v___x_945_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v_structId_965_, lean_object* v___x_966_, lean_object* v_goal_967_, lean_object* v_as_968_, lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_978_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_965_, v___x_966_, v_goal_967_, v_as_968_, v_sz_boxed_977_, v_i_boxed_978_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v_as_968_);
lean_dec_ref(v_goal_967_);
lean_dec_ref(v___x_966_);
lean_dec(v_structId_965_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v_structId_980_, lean_object* v___x_981_, lean_object* v_goal_982_, lean_object* v_as_983_, size_t v_sz_984_, size_t v_i_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_985_, v_sz_984_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_b_986_);
return v___x_993_;
}
else
{
lean_object* v_snd_994_; lean_object* v_a_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1024_; 
v_snd_994_ = lean_ctor_get(v_b_986_, 1);
lean_inc(v_snd_994_);
lean_dec_ref(v_b_986_);
v_a_995_ = lean_array_uget(v_as_983_, v_i_985_);
v_fst_996_ = lean_ctor_get(v_a_995_, 0);
v_snd_997_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_999_ = v_a_995_;
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v_a_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_a_1003_; uint8_t v___x_1010_; 
v___x_1001_ = lean_box(0);
v___x_1010_ = lean_nat_dec_eq(v_structId_980_, v_snd_997_);
lean_dec(v_snd_997_);
if (v___x_1010_ == 0)
{
lean_dec(v_fst_996_);
v_a_1003_ = v_snd_994_;
goto v___jp_1002_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_994_, v_fst_996_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_inc(v_fst_996_);
v___x_1012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_981_, v_snd_994_, v_fst_996_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
if (lean_obj_tag(v_a_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1015_; 
v_val_1014_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_a_1013_, 1);
v___x_1015_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_982_, v_fst_996_, v_val_1014_, v_snd_994_);
v_a_1003_ = v___x_1015_;
goto v___jp_1002_;
}
else
{
lean_dec(v_a_1013_);
lean_dec(v_fst_996_);
v_a_1003_ = v_snd_994_;
goto v___jp_1002_;
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_999_);
lean_dec(v_fst_996_);
lean_dec(v_snd_994_);
v_a_1016_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1012_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_dec(v_fst_996_);
v_a_1003_ = v_snd_994_;
goto v___jp_1002_;
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v_a_1003_);
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_a_1003_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_985_, v___x_1006_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_980_, v___x_981_, v_goal_982_, v_as_983_, v_sz_984_, v___x_1007_, v___x_1005_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v_structId_1025_, lean_object* v___x_1026_, lean_object* v_goal_1027_, lean_object* v_as_1028_, lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1025_, v___x_1026_, v_goal_1027_, v_as_1028_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1028_);
lean_dec_ref(v_goal_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_structId_1025_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v_structId_1040_, lean_object* v___x_1041_, lean_object* v_goal_1042_, lean_object* v_t_1043_, lean_object* v_init_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_root_1050_; lean_object* v_tail_1051_; lean_object* v___x_1052_; 
v_root_1050_ = lean_ctor_get(v_t_1043_, 0);
v_tail_1051_ = lean_ctor_get(v_t_1043_, 1);
lean_inc_ref(v_init_1044_);
v___x_1052_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1044_, v_structId_1040_, v___x_1041_, v_goal_1042_, v_root_1050_, v_init_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v_init_1044_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1089_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1089_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1089_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
if (lean_obj_tag(v_a_1053_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v_a_1053_, 1);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; size_t v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1055_);
v_a_1061_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v_a_1053_, 1);
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_a_1061_);
v_sz_1064_ = lean_array_size(v_tail_1051_);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1040_, v___x_1041_, v_goal_1042_, v_tail_1051_, v_sz_1064_, v___x_1065_, v___x_1063_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1080_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1080_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_fst_1071_; 
v_fst_1071_ = lean_ctor_get(v_a_1067_, 0);
if (lean_obj_tag(v_fst_1071_) == 0)
{
lean_object* v_snd_1072_; lean_object* v___x_1074_; 
v_snd_1072_ = lean_ctor_get(v_a_1067_, 1);
lean_inc(v_snd_1072_);
lean_dec(v_a_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_snd_1072_);
v___x_1074_ = v___x_1069_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_snd_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v_val_1076_; lean_object* v___x_1078_; 
lean_inc_ref(v_fst_1071_);
lean_dec(v_a_1067_);
v_val_1076_ = lean_ctor_get(v_fst_1071_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v_fst_1071_, 1);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_val_1076_);
v___x_1078_ = v___x_1069_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_val_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1066_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1066_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1052_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1052_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v_structId_1098_, lean_object* v___x_1099_, lean_object* v_goal_1100_, lean_object* v_t_1101_, lean_object* v_init_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1098_, v___x_1099_, v_goal_1100_, v_t_1101_, v_init_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v_t_1101_);
lean_dec_ref(v_goal_1100_);
lean_dec_ref(v___x_1099_);
lean_dec(v_structId_1098_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1109_, lean_object* v_structId_1110_, lean_object* v_model_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1118_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1117_, v_goal_1109_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_structs_1120_; lean_object* v_exprToStructIdEntries_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v_structs_1120_ = lean_ctor_get(v_a_1119_, 0);
lean_inc_ref(v_structs_1120_);
v_exprToStructIdEntries_1121_ = lean_ctor_get(v_a_1119_, 3);
lean_inc_ref(v_exprToStructIdEntries_1121_);
lean_dec(v_a_1119_);
v___x_1122_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1123_ = lean_array_get(v___x_1122_, v_structs_1120_, v_structId_1110_);
lean_dec_ref(v_structs_1120_);
v___x_1124_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1110_, v___x_1123_, v_goal_1109_, v_exprToStructIdEntries_1121_, v_model_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec_ref(v_exprToStructIdEntries_1121_);
lean_dec(v___x_1123_);
return v___x_1124_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_model_1111_);
v_a_1125_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v___x_1118_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1118_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_ref_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v_ref_1129_ = lean_ctor_get(v_a_1114_, 4);
v___x_1130_ = lean_io_error_to_string(v_a_1125_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_ofFormat(v___x_1131_);
lean_inc(v_ref_1129_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_ref_1129_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1133_);
v___x_1135_ = v___x_1127_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1138_, lean_object* v_structId_1139_, lean_object* v_model_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1138_, v_structId_1139_, v_model_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_structId_1139_);
lean_dec_ref(v_goal_1138_);
return v_res_1146_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1147_, lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1148_, v_a_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_a_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1151_, v_m_1152_, v_a_1153_);
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_m_1152_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1156_, lean_object* v_a_1157_, lean_object* v_x_1158_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1157_, v_x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1160_, lean_object* v_a_1161_, lean_object* v_x_1162_){
_start:
{
uint8_t v_res_1163_; lean_object* v_r_1164_; 
v_res_1163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1160_, v_a_1161_, v_x_1162_);
lean_dec(v_x_1162_);
lean_dec_ref(v_a_1161_);
v_r_1164_ = lean_box(v_res_1163_);
return v_r_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1165_, lean_object* v___x_1166_, lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v___x_1166_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1170_);
return v___x_1177_;
}
else
{
lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1219_; 
v_snd_1178_ = lean_ctor_get(v_b_1170_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; 
v_unused_1220_ = lean_ctor_get(v_b_1170_, 0);
lean_dec(v_unused_1220_);
v___x_1180_ = v_b_1170_;
v_isShared_1181_ = v_isSharedCheck_1219_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_dec(v_b_1170_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1219_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
lean_inc(v_a_1182_);
v___x_1183_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1165_, v_a_1182_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v_a_1187_; uint8_t v___x_1194_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_box(0);
v___x_1194_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1184_);
if (v___x_1194_ == 0)
{
lean_dec(v_a_1184_);
v_a_1187_ = v_snd_1178_;
goto v___jp_1186_;
}
else
{
lean_object* v_type_1195_; lean_object* v___x_1196_; 
v_type_1195_ = lean_ctor_get(v___x_1166_, 2);
lean_inc(v_a_1184_);
lean_inc_ref(v_type_1195_);
v___x_1196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1195_, v_a_1184_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; uint8_t v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_unbox(v_a_1197_);
lean_dec(v_a_1197_);
if (v___x_1198_ == 0)
{
lean_dec(v_a_1184_);
v_a_1187_ = v_snd_1178_;
goto v___jp_1186_;
}
else
{
lean_object* v_self_1199_; lean_object* v___x_1200_; 
v_self_1199_ = lean_ctor_get(v_a_1184_, 0);
lean_inc_ref(v_self_1199_);
lean_dec(v_a_1184_);
v___x_1200_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1166_, v_self_1199_);
if (lean_obj_tag(v___x_1200_) == 1)
{
lean_object* v_val_1201_; lean_object* v___x_1202_; 
v_val_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1165_, v_self_1199_, v_val_1201_, v_snd_1178_);
v_a_1187_ = v___x_1202_;
goto v___jp_1186_;
}
else
{
lean_dec(v___x_1200_);
lean_dec_ref(v_self_1199_);
v_a_1187_ = v_snd_1178_;
goto v___jp_1186_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_a_1184_);
lean_del_object(v___x_1180_);
lean_dec(v_snd_1178_);
lean_dec_ref(v___x_1166_);
v_a_1203_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1196_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1196_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
v___jp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1187_);
lean_ctor_set(v___x_1180_, 0, v___x_1185_);
v___x_1189_ = v___x_1180_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_a_1187_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
size_t v___x_1190_; size_t v___x_1191_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1169_, v___x_1190_);
v_i_1169_ = v___x_1191_;
v_b_1170_ = v___x_1189_;
goto _start;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_del_object(v___x_1180_);
lean_dec(v_snd_1178_);
lean_dec_ref(v___x_1166_);
v_a_1211_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1183_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1183_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1221_, lean_object* v___x_1222_, lean_object* v_as_1223_, lean_object* v_sz_1224_, lean_object* v_i_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
size_t v_sz_boxed_1232_; size_t v_i_boxed_1233_; lean_object* v_res_1234_; 
v_sz_boxed_1232_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1233_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_res_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1221_, v___x_1222_, v_as_1223_, v_sz_boxed_1232_, v_i_boxed_1233_, v_b_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v_as_1223_);
lean_dec_ref(v_goal_1221_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1235_, lean_object* v___x_1236_, lean_object* v_as_1237_, size_t v_sz_1238_, size_t v_i_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref(v___x_1236_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_b_1240_);
return v___x_1247_;
}
else
{
lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1289_; 
v_snd_1248_ = lean_ctor_get(v_b_1240_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_b_1240_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_b_1240_, 0);
lean_dec(v_unused_1290_);
v___x_1250_ = v_b_1240_;
v_isShared_1251_ = v_isSharedCheck_1289_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_dec(v_b_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1289_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_array_uget_borrowed(v_as_1237_, v_i_1239_);
lean_inc(v_a_1252_);
v___x_1253_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1235_, v_a_1252_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v_a_1257_; uint8_t v___x_1264_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = lean_box(0);
v___x_1264_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1254_);
if (v___x_1264_ == 0)
{
lean_dec(v_a_1254_);
v_a_1257_ = v_snd_1248_;
goto v___jp_1256_;
}
else
{
lean_object* v_type_1265_; lean_object* v___x_1266_; 
v_type_1265_ = lean_ctor_get(v___x_1236_, 2);
lean_inc(v_a_1254_);
lean_inc_ref(v_type_1265_);
v___x_1266_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1265_, v_a_1254_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = lean_unbox(v_a_1267_);
lean_dec(v_a_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v_a_1254_);
v_a_1257_ = v_snd_1248_;
goto v___jp_1256_;
}
else
{
lean_object* v_self_1269_; lean_object* v___x_1270_; 
v_self_1269_ = lean_ctor_get(v_a_1254_, 0);
lean_inc_ref(v_self_1269_);
lean_dec(v_a_1254_);
v___x_1270_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1236_, v_self_1269_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; 
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1235_, v_self_1269_, v_val_1271_, v_snd_1248_);
v_a_1257_ = v___x_1272_;
goto v___jp_1256_;
}
else
{
lean_dec(v___x_1270_);
lean_dec_ref(v_self_1269_);
v_a_1257_ = v_snd_1248_;
goto v___jp_1256_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1254_);
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec_ref(v___x_1236_);
v_a_1273_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1266_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1266_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
v___jp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_a_1257_);
lean_ctor_set(v___x_1250_, 0, v___x_1255_);
v___x_1259_ = v___x_1250_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1257_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_add(v_i_1239_, v___x_1260_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1235_, v___x_1236_, v_as_1237_, v_sz_1238_, v___x_1261_, v___x_1259_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec_ref(v___x_1236_);
v_a_1281_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1253_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1253_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1291_, lean_object* v___x_1292_, lean_object* v_as_1293_, lean_object* v_sz_1294_, lean_object* v_i_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
size_t v_sz_boxed_1302_; size_t v_i_boxed_1303_; lean_object* v_res_1304_; 
v_sz_boxed_1302_ = lean_unbox_usize(v_sz_1294_);
lean_dec(v_sz_1294_);
v_i_boxed_1303_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1291_, v___x_1292_, v_as_1293_, v_sz_boxed_1302_, v_i_boxed_1303_, v_b_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_as_1293_);
lean_dec_ref(v_goal_1291_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1305_, lean_object* v_goal_1306_, lean_object* v___x_1307_, lean_object* v_n_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
if (lean_obj_tag(v_n_1308_) == 0)
{
lean_object* v_cs_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; size_t v_sz_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v_cs_1315_ = lean_ctor_get(v_n_1308_, 0);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_b_1309_);
v_sz_1318_ = lean_array_size(v_cs_1315_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1305_, v_goal_1306_, v___x_1307_, v_cs_1315_, v_sz_1318_, v___x_1319_, v___x_1317_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1335_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_fst_1325_; 
v_fst_1325_ = lean_ctor_get(v_a_1321_, 0);
if (lean_obj_tag(v_fst_1325_) == 0)
{
lean_object* v_snd_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v_snd_1326_ = lean_ctor_get(v_a_1321_, 1);
lean_inc(v_snd_1326_);
lean_dec(v_a_1321_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_snd_1326_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; 
lean_inc_ref(v_fst_1325_);
lean_dec(v_a_1321_);
v_val_1331_ = lean_ctor_get(v_fst_1325_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_fst_1325_, 1);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_val_1331_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_val_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1320_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1320_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_vs_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v_vs_1344_ = lean_ctor_get(v_n_1308_, 0);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_b_1309_);
v_sz_1347_ = lean_array_size(v_vs_1344_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1306_, v___x_1307_, v_vs_1344_, v_sz_1347_, v___x_1348_, v___x_1346_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1364_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_fst_1354_; 
v_fst_1354_ = lean_ctor_get(v_a_1350_, 0);
if (lean_obj_tag(v_fst_1354_) == 0)
{
lean_object* v_snd_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v_snd_1355_ = lean_ctor_get(v_a_1350_, 1);
lean_inc(v_snd_1355_);
lean_dec(v_a_1350_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_snd_1355_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1356_);
v___x_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
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
lean_inc_ref(v_fst_1354_);
lean_dec(v_a_1350_);
v_val_1360_ = lean_ctor_get(v_fst_1354_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_fst_1354_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_val_1360_);
v___x_1362_ = v___x_1352_;
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
v_a_1365_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1349_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1349_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1373_, lean_object* v_goal_1374_, lean_object* v___x_1375_, lean_object* v_as_1376_, size_t v_sz_1377_, size_t v_i_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_lt(v_i_1378_, v_sz_1377_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref(v___x_1375_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_b_1379_);
return v___x_1386_;
}
else
{
lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1421_; 
v_snd_1387_ = lean_ctor_get(v_b_1379_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_b_1379_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_b_1379_, 0);
lean_dec(v_unused_1422_);
v___x_1389_ = v_b_1379_;
v_isShared_1390_ = v_isSharedCheck_1421_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_dec(v_b_1379_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1421_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_a_1391_; lean_object* v___x_1392_; 
v_a_1391_ = lean_array_uget_borrowed(v_as_1376_, v_i_1378_);
lean_inc(v_snd_1387_);
lean_inc_ref(v___x_1375_);
v___x_1392_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1373_, v_goal_1374_, v___x_1375_, v_a_1391_, v_snd_1387_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1412_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1412_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1412_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
if (lean_obj_tag(v_a_1393_) == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec_ref(v___x_1375_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1393_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1397_);
v___x_1399_ = v___x_1389_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1387_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1401_ = v___x_1395_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_del_object(v___x_1395_);
lean_dec(v_snd_1387_);
v_a_1404_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v_a_1393_, 1);
v___x_1405_ = lean_box(0);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_a_1404_);
lean_ctor_set(v___x_1389_, 0, v___x_1405_);
v___x_1407_ = v___x_1389_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_a_1404_);
v___x_1407_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
size_t v___x_1408_; size_t v___x_1409_; 
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1378_, v___x_1408_);
v_i_1378_ = v___x_1409_;
v_b_1379_ = v___x_1407_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_del_object(v___x_1389_);
lean_dec(v_snd_1387_);
lean_dec_ref(v___x_1375_);
v_a_1413_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1392_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1392_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1423_, lean_object* v_goal_1424_, lean_object* v___x_1425_, lean_object* v_as_1426_, lean_object* v_sz_1427_, lean_object* v_i_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
size_t v_sz_boxed_1435_; size_t v_i_boxed_1436_; lean_object* v_res_1437_; 
v_sz_boxed_1435_ = lean_unbox_usize(v_sz_1427_);
lean_dec(v_sz_1427_);
v_i_boxed_1436_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1423_, v_goal_1424_, v___x_1425_, v_as_1426_, v_sz_boxed_1435_, v_i_boxed_1436_, v_b_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_as_1426_);
lean_dec_ref(v_goal_1424_);
lean_dec_ref(v_init_1423_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1438_, lean_object* v_goal_1439_, lean_object* v___x_1440_, lean_object* v_n_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1438_, v_goal_1439_, v___x_1440_, v_n_1441_, v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec_ref(v_n_1441_);
lean_dec_ref(v_goal_1439_);
lean_dec_ref(v_init_1438_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1449_, lean_object* v___x_1450_, lean_object* v_as_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_dec_ref(v___x_1450_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_b_1454_);
return v___x_1461_;
}
else
{
lean_object* v_snd_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1503_; 
v_snd_1462_ = lean_ctor_get(v_b_1454_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_b_1454_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_b_1454_, 0);
lean_dec(v_unused_1504_);
v___x_1464_ = v_b_1454_;
v_isShared_1465_ = v_isSharedCheck_1503_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snd_1462_);
lean_dec(v_b_1454_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1503_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_array_uget_borrowed(v_as_1451_, v_i_1453_);
lean_inc(v_a_1466_);
v___x_1467_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1449_, v_a_1466_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v_a_1471_; uint8_t v___x_1478_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___x_1469_ = lean_box(0);
v___x_1478_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1468_);
if (v___x_1478_ == 0)
{
lean_dec(v_a_1468_);
v_a_1471_ = v_snd_1462_;
goto v___jp_1470_;
}
else
{
lean_object* v_type_1479_; lean_object* v___x_1480_; 
v_type_1479_ = lean_ctor_get(v___x_1450_, 2);
lean_inc(v_a_1468_);
lean_inc_ref(v_type_1479_);
v___x_1480_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1479_, v_a_1468_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; uint8_t v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = lean_unbox(v_a_1481_);
lean_dec(v_a_1481_);
if (v___x_1482_ == 0)
{
lean_dec(v_a_1468_);
v_a_1471_ = v_snd_1462_;
goto v___jp_1470_;
}
else
{
lean_object* v_self_1483_; lean_object* v___x_1484_; 
v_self_1483_ = lean_ctor_get(v_a_1468_, 0);
lean_inc_ref(v_self_1483_);
lean_dec(v_a_1468_);
v___x_1484_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1450_, v_self_1483_);
if (lean_obj_tag(v___x_1484_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; 
v_val_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1449_, v_self_1483_, v_val_1485_, v_snd_1462_);
v_a_1471_ = v___x_1486_;
goto v___jp_1470_;
}
else
{
lean_dec(v___x_1484_);
lean_dec_ref(v_self_1483_);
v_a_1471_ = v_snd_1462_;
goto v___jp_1470_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1468_);
lean_del_object(v___x_1464_);
lean_dec(v_snd_1462_);
lean_dec_ref(v___x_1450_);
v_a_1487_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1480_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1480_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
v___jp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v_a_1471_);
lean_ctor_set(v___x_1464_, 0, v___x_1469_);
v___x_1473_ = v___x_1464_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_a_1471_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
size_t v___x_1474_; size_t v___x_1475_; 
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_add(v_i_1453_, v___x_1474_);
v_i_1453_ = v___x_1475_;
v_b_1454_ = v___x_1473_;
goto _start;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_del_object(v___x_1464_);
lean_dec(v_snd_1462_);
lean_dec_ref(v___x_1450_);
v_a_1495_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1467_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1467_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1505_, lean_object* v___x_1506_, lean_object* v_as_1507_, lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1505_, v___x_1506_, v_as_1507_, v_sz_boxed_1516_, v_i_boxed_1517_, v_b_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec_ref(v_as_1507_);
lean_dec_ref(v_goal_1505_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1519_, lean_object* v___x_1520_, lean_object* v_as_1521_, size_t v_sz_1522_, size_t v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_usize_dec_lt(v_i_1523_, v_sz_1522_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec_ref(v___x_1520_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_b_1524_);
return v___x_1531_;
}
else
{
lean_object* v_snd_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1573_; 
v_snd_1532_ = lean_ctor_get(v_b_1524_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_b_1524_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_b_1524_, 0);
lean_dec(v_unused_1574_);
v___x_1534_ = v_b_1524_;
v_isShared_1535_ = v_isSharedCheck_1573_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_snd_1532_);
lean_dec(v_b_1524_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1573_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_array_uget_borrowed(v_as_1521_, v_i_1523_);
lean_inc(v_a_1536_);
v___x_1537_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1519_, v_a_1536_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v_a_1541_; uint8_t v___x_1548_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = lean_box(0);
v___x_1548_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1538_);
if (v___x_1548_ == 0)
{
lean_dec(v_a_1538_);
v_a_1541_ = v_snd_1532_;
goto v___jp_1540_;
}
else
{
lean_object* v_type_1549_; lean_object* v___x_1550_; 
v_type_1549_ = lean_ctor_get(v___x_1520_, 2);
lean_inc(v_a_1538_);
lean_inc_ref(v_type_1549_);
v___x_1550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1549_, v_a_1538_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; uint8_t v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v_a_1538_);
v_a_1541_ = v_snd_1532_;
goto v___jp_1540_;
}
else
{
lean_object* v_self_1553_; lean_object* v___x_1554_; 
v_self_1553_ = lean_ctor_get(v_a_1538_, 0);
lean_inc_ref(v_self_1553_);
lean_dec(v_a_1538_);
v___x_1554_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1520_, v_self_1553_);
if (lean_obj_tag(v___x_1554_) == 1)
{
lean_object* v_val_1555_; lean_object* v___x_1556_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1519_, v_self_1553_, v_val_1555_, v_snd_1532_);
v_a_1541_ = v___x_1556_;
goto v___jp_1540_;
}
else
{
lean_dec(v___x_1554_);
lean_dec_ref(v_self_1553_);
v_a_1541_ = v_snd_1532_;
goto v___jp_1540_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1538_);
lean_del_object(v___x_1534_);
lean_dec(v_snd_1532_);
lean_dec_ref(v___x_1520_);
v_a_1557_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1550_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1550_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
v___jp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v_a_1541_);
lean_ctor_set(v___x_1534_, 0, v___x_1539_);
v___x_1543_ = v___x_1534_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1541_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((size_t)1ULL);
v___x_1545_ = lean_usize_add(v_i_1523_, v___x_1544_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1519_, v___x_1520_, v_as_1521_, v_sz_1522_, v___x_1545_, v___x_1543_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_del_object(v___x_1534_);
lean_dec(v_snd_1532_);
lean_dec_ref(v___x_1520_);
v_a_1565_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1537_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1537_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1575_, lean_object* v___x_1576_, lean_object* v_as_1577_, lean_object* v_sz_1578_, lean_object* v_i_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
size_t v_sz_boxed_1586_; size_t v_i_boxed_1587_; lean_object* v_res_1588_; 
v_sz_boxed_1586_ = lean_unbox_usize(v_sz_1578_);
lean_dec(v_sz_1578_);
v_i_boxed_1587_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1575_, v___x_1576_, v_as_1577_, v_sz_boxed_1586_, v_i_boxed_1587_, v_b_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_as_1577_);
lean_dec_ref(v_goal_1575_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1589_, lean_object* v___x_1590_, lean_object* v_t_1591_, lean_object* v_init_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_root_1598_; lean_object* v_tail_1599_; lean_object* v___x_1600_; 
v_root_1598_ = lean_ctor_get(v_t_1591_, 0);
v_tail_1599_ = lean_ctor_get(v_t_1591_, 1);
lean_inc_ref(v___x_1590_);
lean_inc_ref(v_init_1592_);
v___x_1600_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1592_, v_goal_1589_, v___x_1590_, v_root_1598_, v_init_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec_ref(v_init_1592_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1637_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1637_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1637_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
if (lean_obj_tag(v_a_1601_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; 
lean_dec_ref(v___x_1590_);
v_a_1605_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v_a_1601_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_a_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
lean_del_object(v___x_1603_);
v_a_1609_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1609_);
v_sz_1612_ = lean_array_size(v_tail_1599_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1589_, v___x_1590_, v_tail_1599_, v_sz_1612_, v___x_1613_, v___x_1611_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1628_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1628_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1628_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_fst_1619_; 
v_fst_1619_ = lean_ctor_get(v_a_1615_, 0);
if (lean_obj_tag(v_fst_1619_) == 0)
{
lean_object* v_snd_1620_; lean_object* v___x_1622_; 
v_snd_1620_ = lean_ctor_get(v_a_1615_, 1);
lean_inc(v_snd_1620_);
lean_dec(v_a_1615_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_snd_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_snd_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v_val_1624_; lean_object* v___x_1626_; 
lean_inc_ref(v_fst_1619_);
lean_dec(v_a_1615_);
v_val_1624_ = lean_ctor_get(v_fst_1619_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_fst_1619_, 1);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_val_1624_);
v___x_1626_ = v___x_1617_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_val_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1614_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1614_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___x_1590_);
v_a_1638_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1600_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1600_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1646_, lean_object* v___x_1647_, lean_object* v_t_1648_, lean_object* v_init_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1646_, v___x_1647_, v_t_1648_, v_init_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_t_1648_);
lean_dec_ref(v_goal_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1656_, lean_object* v_as_1657_, size_t v_sz_1658_, size_t v_i_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1659_, v_sz_1658_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_b_1660_);
return v___x_1667_;
}
else
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1699_; 
v_snd_1668_ = lean_ctor_get(v_b_1660_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_b_1660_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_b_1660_, 0);
lean_dec(v_unused_1700_);
v___x_1670_ = v_b_1660_;
v_isShared_1671_ = v_isSharedCheck_1699_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v_b_1660_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1699_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_array_uget_borrowed(v_as_1657_, v_i_1659_);
lean_inc(v_a_1672_);
v___x_1673_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1656_, v_a_1672_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_self_1675_; lean_object* v___x_1676_; lean_object* v_a_1678_; lean_object* v___x_1685_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_self_1675_ = lean_ctor_get(v_a_1674_, 0);
lean_inc_ref_n(v_self_1675_, 2);
lean_dec(v_a_1674_);
v___x_1676_ = lean_box(0);
v___x_1685_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1675_);
if (lean_obj_tag(v___x_1685_) == 1)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; 
v_val_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1668_, v_val_1686_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1668_, v_self_1675_);
lean_dec_ref(v_self_1675_);
if (lean_obj_tag(v___x_1688_) == 1)
{
lean_object* v_val_1689_; lean_object* v___x_1690_; 
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1656_, v_val_1686_, v_val_1689_, v_snd_1668_);
v_a_1678_ = v___x_1690_;
goto v___jp_1677_;
}
else
{
lean_dec(v___x_1688_);
lean_dec(v_val_1686_);
v_a_1678_ = v_snd_1668_;
goto v___jp_1677_;
}
}
else
{
lean_dec_ref_known(v___x_1687_, 1);
lean_dec(v_val_1686_);
lean_dec_ref(v_self_1675_);
v_a_1678_ = v_snd_1668_;
goto v___jp_1677_;
}
}
else
{
lean_dec(v___x_1685_);
lean_dec_ref(v_self_1675_);
v_a_1678_ = v_snd_1668_;
goto v___jp_1677_;
}
v___jp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_a_1678_);
lean_ctor_set(v___x_1670_, 0, v___x_1676_);
v___x_1680_ = v___x_1670_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_a_1678_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
size_t v___x_1681_; size_t v___x_1682_; 
v___x_1681_ = ((size_t)1ULL);
v___x_1682_ = lean_usize_add(v_i_1659_, v___x_1681_);
v_i_1659_ = v___x_1682_;
v_b_1660_ = v___x_1680_;
goto _start;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1670_);
lean_dec(v_snd_1668_);
v_a_1691_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1673_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1673_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1701_, lean_object* v_as_1702_, lean_object* v_sz_1703_, lean_object* v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
size_t v_sz_boxed_1711_; size_t v_i_boxed_1712_; lean_object* v_res_1713_; 
v_sz_boxed_1711_ = lean_unbox_usize(v_sz_1703_);
lean_dec(v_sz_1703_);
v_i_boxed_1712_ = lean_unbox_usize(v_i_1704_);
lean_dec(v_i_1704_);
v_res_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1701_, v_as_1702_, v_sz_boxed_1711_, v_i_boxed_1712_, v_b_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_as_1702_);
lean_dec_ref(v_goal_1701_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1714_, lean_object* v_as_1715_, size_t v_sz_1716_, size_t v_i_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_lt(v_i_1717_, v_sz_1716_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1718_);
return v___x_1725_;
}
else
{
lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1757_; 
v_snd_1726_ = lean_ctor_get(v_b_1718_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_b_1718_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_b_1718_, 0);
lean_dec(v_unused_1758_);
v___x_1728_ = v_b_1718_;
v_isShared_1729_ = v_isSharedCheck_1757_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_dec(v_b_1718_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1757_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_a_1730_; lean_object* v___x_1731_; 
v_a_1730_ = lean_array_uget_borrowed(v_as_1715_, v_i_1717_);
lean_inc(v_a_1730_);
v___x_1731_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1714_, v_a_1730_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v_self_1733_; lean_object* v___x_1734_; lean_object* v_a_1736_; lean_object* v___x_1743_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v_self_1733_ = lean_ctor_get(v_a_1732_, 0);
lean_inc_ref_n(v_self_1733_, 2);
lean_dec(v_a_1732_);
v___x_1734_ = lean_box(0);
v___x_1743_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1733_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1745_; 
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1726_, v_val_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1726_, v_self_1733_);
lean_dec_ref(v_self_1733_);
if (lean_obj_tag(v___x_1746_) == 1)
{
lean_object* v_val_1747_; lean_object* v___x_1748_; 
v_val_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1714_, v_val_1744_, v_val_1747_, v_snd_1726_);
v_a_1736_ = v___x_1748_;
goto v___jp_1735_;
}
else
{
lean_dec(v___x_1746_);
lean_dec(v_val_1744_);
v_a_1736_ = v_snd_1726_;
goto v___jp_1735_;
}
}
else
{
lean_dec_ref_known(v___x_1745_, 1);
lean_dec(v_val_1744_);
lean_dec_ref(v_self_1733_);
v_a_1736_ = v_snd_1726_;
goto v___jp_1735_;
}
}
else
{
lean_dec(v___x_1743_);
lean_dec_ref(v_self_1733_);
v_a_1736_ = v_snd_1726_;
goto v___jp_1735_;
}
v___jp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_a_1736_);
lean_ctor_set(v___x_1728_, 0, v___x_1734_);
v___x_1738_ = v___x_1728_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_a_1736_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1717_, v___x_1739_);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1714_, v_as_1715_, v_sz_1716_, v___x_1740_, v___x_1738_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
v_a_1749_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1731_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1731_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1759_, lean_object* v_as_1760_, lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1759_, v_as_1760_, v_sz_boxed_1769_, v_i_boxed_1770_, v_b_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_as_1760_);
lean_dec_ref(v_goal_1759_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1772_, lean_object* v_as_1773_, size_t v_sz_1774_, size_t v_i_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_usize_dec_lt(v_i_1775_, v_sz_1774_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_b_1776_);
return v___x_1783_;
}
else
{
lean_object* v_snd_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1815_; 
v_snd_1784_ = lean_ctor_get(v_b_1776_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_b_1776_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_b_1776_, 0);
lean_dec(v_unused_1816_);
v___x_1786_ = v_b_1776_;
v_isShared_1787_ = v_isSharedCheck_1815_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_snd_1784_);
lean_dec(v_b_1776_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1815_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_a_1788_; lean_object* v___x_1789_; 
v_a_1788_ = lean_array_uget_borrowed(v_as_1773_, v_i_1775_);
lean_inc(v_a_1788_);
v___x_1789_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1772_, v_a_1788_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_self_1791_; lean_object* v___x_1792_; lean_object* v_a_1794_; lean_object* v___x_1801_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v_self_1791_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref_n(v_self_1791_, 2);
lean_dec(v_a_1790_);
v___x_1792_ = lean_box(0);
v___x_1801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1791_);
if (lean_obj_tag(v___x_1801_) == 1)
{
lean_object* v_val_1802_; lean_object* v___x_1803_; 
v_val_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_val_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1784_, v_val_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1784_, v_self_1791_);
lean_dec_ref(v_self_1791_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; 
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1772_, v_val_1802_, v_val_1805_, v_snd_1784_);
v_a_1794_ = v___x_1806_;
goto v___jp_1793_;
}
else
{
lean_dec(v___x_1804_);
lean_dec(v_val_1802_);
v_a_1794_ = v_snd_1784_;
goto v___jp_1793_;
}
}
else
{
lean_dec_ref_known(v___x_1803_, 1);
lean_dec(v_val_1802_);
lean_dec_ref(v_self_1791_);
v_a_1794_ = v_snd_1784_;
goto v___jp_1793_;
}
}
else
{
lean_dec(v___x_1801_);
lean_dec_ref(v_self_1791_);
v_a_1794_ = v_snd_1784_;
goto v___jp_1793_;
}
v___jp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v_a_1794_);
lean_ctor_set(v___x_1786_, 0, v___x_1792_);
v___x_1796_ = v___x_1786_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1794_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
size_t v___x_1797_; size_t v___x_1798_; 
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1775_, v___x_1797_);
v_i_1775_ = v___x_1798_;
v_b_1776_ = v___x_1796_;
goto _start;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_del_object(v___x_1786_);
lean_dec(v_snd_1784_);
v_a_1807_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1789_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1789_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1817_, lean_object* v_as_1818_, lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
size_t v_sz_boxed_1827_; size_t v_i_boxed_1828_; lean_object* v_res_1829_; 
v_sz_boxed_1827_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1828_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1817_, v_as_1818_, v_sz_boxed_1827_, v_i_boxed_1828_, v_b_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1818_);
lean_dec_ref(v_goal_1817_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1830_, lean_object* v_as_1831_, size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_lt(v_i_1833_, v_sz_1832_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1834_);
return v___x_1841_;
}
else
{
lean_object* v_snd_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1873_; 
v_snd_1842_ = lean_ctor_get(v_b_1834_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_b_1834_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_b_1834_, 0);
lean_dec(v_unused_1874_);
v___x_1844_ = v_b_1834_;
v_isShared_1845_ = v_isSharedCheck_1873_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snd_1842_);
lean_dec(v_b_1834_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1873_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_array_uget_borrowed(v_as_1831_, v_i_1833_);
lean_inc(v_a_1846_);
v___x_1847_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1830_, v_a_1846_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_self_1849_; lean_object* v___x_1850_; lean_object* v_a_1852_; lean_object* v___x_1859_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v_self_1849_ = lean_ctor_get(v_a_1848_, 0);
lean_inc_ref_n(v_self_1849_, 2);
lean_dec(v_a_1848_);
v___x_1850_ = lean_box(0);
v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1849_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1861_; 
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1842_, v_val_1860_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1842_, v_self_1849_);
lean_dec_ref(v_self_1849_);
if (lean_obj_tag(v___x_1862_) == 1)
{
lean_object* v_val_1863_; lean_object* v___x_1864_; 
v_val_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_val_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1830_, v_val_1860_, v_val_1863_, v_snd_1842_);
v_a_1852_ = v___x_1864_;
goto v___jp_1851_;
}
else
{
lean_dec(v___x_1862_);
lean_dec(v_val_1860_);
v_a_1852_ = v_snd_1842_;
goto v___jp_1851_;
}
}
else
{
lean_dec_ref_known(v___x_1861_, 1);
lean_dec(v_val_1860_);
lean_dec_ref(v_self_1849_);
v_a_1852_ = v_snd_1842_;
goto v___jp_1851_;
}
}
else
{
lean_dec(v___x_1859_);
lean_dec_ref(v_self_1849_);
v_a_1852_ = v_snd_1842_;
goto v___jp_1851_;
}
v___jp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v_a_1852_);
lean_ctor_set(v___x_1844_, 0, v___x_1850_);
v___x_1854_ = v___x_1844_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1833_, v___x_1855_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1830_, v_as_1831_, v_sz_1832_, v___x_1856_, v___x_1854_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1844_);
lean_dec(v_snd_1842_);
v_a_1865_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1847_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1847_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1875_, lean_object* v_as_1876_, lean_object* v_sz_1877_, lean_object* v_i_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
size_t v_sz_boxed_1885_; size_t v_i_boxed_1886_; lean_object* v_res_1887_; 
v_sz_boxed_1885_ = lean_unbox_usize(v_sz_1877_);
lean_dec(v_sz_1877_);
v_i_boxed_1886_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_res_1887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1875_, v_as_1876_, v_sz_boxed_1885_, v_i_boxed_1886_, v_b_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec_ref(v_as_1876_);
lean_dec_ref(v_goal_1875_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1888_, lean_object* v_goal_1889_, lean_object* v_n_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
if (lean_obj_tag(v_n_1890_) == 0)
{
lean_object* v_cs_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; size_t v_sz_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v_cs_1897_ = lean_ctor_get(v_n_1890_, 0);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_b_1891_);
v_sz_1900_ = lean_array_size(v_cs_1897_);
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1888_, v_goal_1889_, v_cs_1897_, v_sz_1900_, v___x_1901_, v___x_1899_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1917_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_fst_1907_; 
v_fst_1907_ = lean_ctor_get(v_a_1903_, 0);
if (lean_obj_tag(v_fst_1907_) == 0)
{
lean_object* v_snd_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v_snd_1908_ = lean_ctor_get(v_a_1903_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1903_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_snd_1908_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1909_);
v___x_1911_ = v___x_1905_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v_val_1913_; lean_object* v___x_1915_; 
lean_inc_ref(v_fst_1907_);
lean_dec(v_a_1903_);
v_val_1913_ = lean_ctor_get(v_fst_1907_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v_fst_1907_, 1);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v_val_1913_);
v___x_1915_ = v___x_1905_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_val_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1902_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1902_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_vs_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; size_t v_sz_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v_vs_1926_ = lean_ctor_get(v_n_1890_, 0);
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v_b_1891_);
v_sz_1929_ = lean_array_size(v_vs_1926_);
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1889_, v_vs_1926_, v_sz_1929_, v___x_1930_, v___x_1928_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1946_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1946_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1946_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_fst_1936_; 
v_fst_1936_ = lean_ctor_get(v_a_1932_, 0);
if (lean_obj_tag(v_fst_1936_) == 0)
{
lean_object* v_snd_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v_snd_1937_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1937_);
lean_dec(v_a_1932_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_snd_1937_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1938_);
v___x_1940_ = v___x_1934_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
else
{
lean_object* v_val_1942_; lean_object* v___x_1944_; 
lean_inc_ref(v_fst_1936_);
lean_dec(v_a_1932_);
v_val_1942_ = lean_ctor_get(v_fst_1936_, 0);
lean_inc(v_val_1942_);
lean_dec_ref_known(v_fst_1936_, 1);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_val_1942_);
v___x_1944_ = v___x_1934_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_val_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1931_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1931_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1955_, lean_object* v_goal_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, size_t v_i_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1960_);
return v___x_1967_;
}
else
{
lean_object* v_snd_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2002_; 
v_snd_1968_ = lean_ctor_get(v_b_1960_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_b_1960_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v_b_1960_, 0);
lean_dec(v_unused_2003_);
v___x_1970_ = v_b_1960_;
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_snd_1968_);
lean_dec(v_b_1960_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_array_uget_borrowed(v_as_1957_, v_i_1959_);
lean_inc(v_snd_1968_);
v___x_1973_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1955_, v_goal_1956_, v_a_1972_, v_snd_1968_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1993_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
if (lean_obj_tag(v_a_1974_) == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_a_1974_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1978_);
v___x_1980_ = v___x_1970_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_snd_1968_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1980_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_del_object(v___x_1976_);
lean_dec(v_snd_1968_);
v_a_1985_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v_a_1974_, 1);
v___x_1986_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v_a_1985_);
lean_ctor_set(v___x_1970_, 0, v___x_1986_);
v___x_1988_ = v___x_1970_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_a_1985_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
size_t v___x_1989_; size_t v___x_1990_; 
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1959_, v___x_1989_);
v_i_1959_ = v___x_1990_;
v_b_1960_ = v___x_1988_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_del_object(v___x_1970_);
lean_dec(v_snd_1968_);
v_a_1994_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1973_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1973_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2004_, lean_object* v_goal_2005_, lean_object* v_as_2006_, lean_object* v_sz_2007_, lean_object* v_i_2008_, lean_object* v_b_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
size_t v_sz_boxed_2015_; size_t v_i_boxed_2016_; lean_object* v_res_2017_; 
v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2007_);
lean_dec(v_sz_2007_);
v_i_boxed_2016_ = lean_unbox_usize(v_i_2008_);
lean_dec(v_i_2008_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2004_, v_goal_2005_, v_as_2006_, v_sz_boxed_2015_, v_i_boxed_2016_, v_b_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v_as_2006_);
lean_dec_ref(v_goal_2005_);
lean_dec_ref(v_init_2004_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2018_, lean_object* v_goal_2019_, lean_object* v_n_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2018_, v_goal_2019_, v_n_2020_, v_b_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_n_2020_);
lean_dec_ref(v_goal_2019_);
lean_dec_ref(v_init_2018_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2028_, lean_object* v_t_2029_, lean_object* v_init_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_root_2036_; lean_object* v_tail_2037_; lean_object* v___x_2038_; 
v_root_2036_ = lean_ctor_get(v_t_2029_, 0);
v_tail_2037_ = lean_ctor_get(v_t_2029_, 1);
lean_inc_ref(v_init_2030_);
v___x_2038_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2030_, v_goal_2028_, v_root_2036_, v_init_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec_ref(v_init_2030_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2075_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2075_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2075_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
if (lean_obj_tag(v_a_2039_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; 
v_a_2043_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v_a_2039_, 1);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_a_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; size_t v_sz_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2041_);
v_a_2047_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v_a_2039_, 1);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v_a_2047_);
v_sz_2050_ = lean_array_size(v_tail_2037_);
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2028_, v_tail_2037_, v_sz_2050_, v___x_2051_, v___x_2049_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2066_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2066_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2066_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_fst_2057_; 
v_fst_2057_ = lean_ctor_get(v_a_2053_, 0);
if (lean_obj_tag(v_fst_2057_) == 0)
{
lean_object* v_snd_2058_; lean_object* v___x_2060_; 
v_snd_2058_ = lean_ctor_get(v_a_2053_, 1);
lean_inc(v_snd_2058_);
lean_dec(v_a_2053_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_snd_2058_);
v___x_2060_ = v___x_2055_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_snd_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
else
{
lean_object* v_val_2062_; lean_object* v___x_2064_; 
lean_inc_ref(v_fst_2057_);
lean_dec(v_a_2053_);
v_val_2062_ = lean_ctor_get(v_fst_2057_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v_fst_2057_, 1);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_val_2062_);
v___x_2064_ = v___x_2055_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_val_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2052_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2052_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2038_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2038_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2084_, lean_object* v_t_2085_, lean_object* v_init_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2084_, v_t_2085_, v_init_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_t_2085_);
lean_dec_ref(v_goal_2084_);
return v_res_2092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_unsigned_to_nat(16u);
v___x_2095_ = lean_mk_array(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_model_2098_; 
v___x_2096_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2097_ = lean_unsigned_to_nat(0u);
v_model_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2098_, 0, v___x_2097_);
lean_ctor_set(v_model_2098_, 1, v___x_2096_);
return v_model_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2106_, lean_object* v_structId_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2114_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2113_, v_goal_2106_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_toGoalState_2116_; lean_object* v_structs_2117_; lean_object* v_exprs_2118_; lean_object* v___x_2119_; lean_object* v_model_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_toGoalState_2116_ = lean_ctor_get(v_goal_2106_, 0);
v_structs_2117_ = lean_ctor_get(v_a_2115_, 0);
lean_inc_ref(v_structs_2117_);
lean_dec(v_a_2115_);
v_exprs_2118_ = lean_ctor_get(v_toGoalState_2116_, 2);
v___x_2119_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2121_ = lean_array_get(v___x_2119_, v_structs_2117_, v_structId_2107_);
lean_dec_ref(v_structs_2117_);
lean_inc(v___x_2121_);
v___x_2122_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2106_, v___x_2121_, v_exprs_2118_, v_model_2120_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2106_, v_structId_2107_, v_a_2123_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2106_, v_exprs_2118_, v_a_2125_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v_type_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_type_2128_ = lean_ctor_get(v___x_2121_, 2);
lean_inc_ref(v_type_2128_);
lean_dec(v___x_2121_);
v___x_2129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2129_, 0, v_type_2128_);
v___x_2130_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2106_, v___x_2129_, v_a_2127_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2133_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2132_, v_a_2131_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2141_);
v___x_2135_ = v___x_2133_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v___x_2133_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_a_2131_);
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2131_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_a_2131_);
v_a_2142_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2133_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2133_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
return v___x_2130_;
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v___x_2121_);
v_a_2150_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2126_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2126_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v___x_2121_);
v_a_2158_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2124_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2124_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v___x_2121_);
v_a_2166_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2122_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2122_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2186_; 
v_a_2174_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2176_ = v___x_2114_;
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2114_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_ref_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v_ref_2178_ = lean_ctor_get(v_a_2110_, 4);
v___x_2179_ = lean_io_error_to_string(v_a_2174_);
v___x_2180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
v___x_2181_ = l_Lean_MessageData_ofFormat(v___x_2180_);
lean_inc(v_ref_2178_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_ref_2178_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2182_);
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2187_, lean_object* v_structId_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2187_, v_structId_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_structId_2188_);
lean_dec_ref(v_goal_2187_);
return v_res_2194_;
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

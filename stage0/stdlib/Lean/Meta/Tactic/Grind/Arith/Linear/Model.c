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
uint8_t lean_bool_not(uint8_t);
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* v_k_x27_8_; uint8_t v___x_9_; 
v_k_x27_8_ = lean_array_fget_borrowed(v_keys_1_, v_i_3_);
v___x_9_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_4_, v_k_x27_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_i_3_, v___x_10_);
lean_dec(v_i_3_);
v_i_3_ = v___x_11_;
goto _start;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_array_fget_borrowed(v_vals_2_, v_i_3_);
lean_dec(v_i_3_);
lean_inc(v___x_13_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_15_, lean_object* v_vals_16_, lean_object* v_i_17_, lean_object* v_k_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_15_, v_vals_16_, v_i_17_, v_k_18_);
lean_dec_ref(v_k_18_);
lean_dec_ref(v_vals_16_);
lean_dec_ref(v_keys_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(lean_object* v_x_20_, size_t v_x_21_, lean_object* v_x_22_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v_es_23_; lean_object* v___x_24_; size_t v___x_25_; size_t v___x_26_; lean_object* v_j_27_; lean_object* v___x_28_; 
v_es_23_ = lean_ctor_get(v_x_20_, 0);
v___x_24_ = lean_box(2);
v___x_25_ = ((size_t)31ULL);
v___x_26_ = lean_usize_land(v_x_21_, v___x_25_);
v_j_27_ = lean_usize_to_nat(v___x_26_);
v___x_28_ = lean_array_get_borrowed(v___x_24_, v_es_23_, v_j_27_);
lean_dec(v_j_27_);
switch(lean_obj_tag(v___x_28_))
{
case 0:
{
lean_object* v_key_29_; lean_object* v_val_30_; uint8_t v___x_31_; 
v_key_29_ = lean_ctor_get(v___x_28_, 0);
v_val_30_ = lean_ctor_get(v___x_28_, 1);
v___x_31_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_22_, v_key_29_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
else
{
lean_object* v___x_33_; 
lean_inc(v_val_30_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_val_30_);
return v___x_33_;
}
}
case 1:
{
lean_object* v_node_34_; size_t v___x_35_; size_t v___x_36_; 
v_node_34_ = lean_ctor_get(v___x_28_, 0);
v___x_35_ = ((size_t)5ULL);
v___x_36_ = lean_usize_shift_right(v_x_21_, v___x_35_);
v_x_20_ = v_node_34_;
v_x_21_ = v___x_36_;
goto _start;
}
default: 
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
}
else
{
lean_object* v_ks_39_; lean_object* v_vs_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_ks_39_ = lean_ctor_get(v_x_20_, 0);
v_vs_40_ = lean_ctor_get(v_x_20_, 1);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_ks_39_, v_vs_40_, v___x_41_, v_x_22_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
size_t v_x_319__boxed_46_; lean_object* v_res_47_; 
v_x_319__boxed_46_ = lean_unbox_usize(v_x_44_);
lean_dec(v_x_44_);
v_res_47_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_43_, v_x_319__boxed_46_, v_x_45_);
lean_dec_ref(v_x_45_);
lean_dec_ref(v_x_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
uint64_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_49_);
v___x_51_ = lean_uint64_to_usize(v___x_50_);
v___x_52_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_48_, v___x_51_, v_x_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_53_, v_x_54_);
lean_dec_ref(v_x_54_);
lean_dec_ref(v_x_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object* v_s_56_, lean_object* v_e_57_){
_start:
{
lean_object* v_varMap_58_; lean_object* v_assignment_59_; lean_object* v___x_60_; 
v_varMap_58_ = lean_ctor_get(v_s_56_, 31);
v_assignment_59_ = lean_ctor_get(v_s_56_, 35);
v___x_60_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_58_, v_e_57_);
if (lean_obj_tag(v___x_60_) == 1)
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_73_; 
v_val_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_73_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_size_65_; uint8_t v___x_66_; 
v_size_65_ = lean_ctor_get(v_assignment_59_, 2);
v___x_66_ = lean_nat_dec_lt(v_val_61_, v_size_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_del_object(v___x_63_);
lean_dec(v_val_61_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = l_instInhabitedRat;
v___x_69_ = l_Lean_PersistentArray_get_x21___redArg(v___x_68_, v_assignment_59_, v_val_61_);
lean_dec(v_val_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_69_);
v___x_71_ = v___x_63_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
else
{
lean_object* v___x_74_; 
lean_dec(v___x_60_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object* v_s_75_, lean_object* v_e_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_75_, v_e_76_);
lean_dec_ref(v_e_76_);
lean_dec_ref(v_s_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object* v_00_u03b2_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object* v_00_u03b2_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_82_, v_x_83_, v_x_84_);
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object* v_00_u03b2_86_, lean_object* v_x_87_, size_t v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_87_, v_x_88_, v_x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_91_, lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
size_t v_x_414__boxed_95_; lean_object* v_res_96_; 
v_x_414__boxed_95_ = lean_unbox_usize(v_x_93_);
lean_dec(v_x_93_);
v_res_96_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_91_, v_x_92_, v_x_414__boxed_95_, v_x_94_);
lean_dec_ref(v_x_94_);
lean_dec_ref(v_x_92_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_97_, lean_object* v_keys_98_, lean_object* v_vals_99_, lean_object* v_heq_100_, lean_object* v_i_101_, lean_object* v_k_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_98_, v_vals_99_, v_i_101_, v_k_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_104_, lean_object* v_keys_105_, lean_object* v_vals_106_, lean_object* v_heq_107_, lean_object* v_i_108_, lean_object* v_k_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_104_, v_keys_105_, v_vals_106_, v_heq_107_, v_i_108_, v_k_109_);
lean_dec_ref(v_k_109_);
lean_dec_ref(v_vals_106_);
lean_dec_ref(v_keys_105_);
return v_res_110_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0(void){
_start:
{
uint8_t v___x_111_; uint64_t v___x_112_; 
v___x_111_ = 1;
v___x_112_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_113_, lean_object* v_n_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_self_120_; lean_object* v___x_121_; uint8_t v_foApprox_122_; uint8_t v_ctxApprox_123_; uint8_t v_quasiPatternApprox_124_; uint8_t v_constApprox_125_; uint8_t v_isDefEqStuckEx_126_; uint8_t v_unificationHints_127_; uint8_t v_proofIrrelevance_128_; uint8_t v_assignSyntheticOpaque_129_; uint8_t v_offsetCnstrs_130_; uint8_t v_etaStruct_131_; uint8_t v_univApprox_132_; uint8_t v_iota_133_; uint8_t v_beta_134_; uint8_t v_proj_135_; uint8_t v_zeta_136_; uint8_t v_zetaDelta_137_; uint8_t v_zetaUnused_138_; uint8_t v_zetaHave_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_176_; 
v_self_120_ = lean_ctor_get(v_n_114_, 0);
lean_inc_ref(v_self_120_);
lean_dec_ref(v_n_114_);
v___x_121_ = l_Lean_Meta_Context_config(v_a_115_);
v_foApprox_122_ = lean_ctor_get_uint8(v___x_121_, 0);
v_ctxApprox_123_ = lean_ctor_get_uint8(v___x_121_, 1);
v_quasiPatternApprox_124_ = lean_ctor_get_uint8(v___x_121_, 2);
v_constApprox_125_ = lean_ctor_get_uint8(v___x_121_, 3);
v_isDefEqStuckEx_126_ = lean_ctor_get_uint8(v___x_121_, 4);
v_unificationHints_127_ = lean_ctor_get_uint8(v___x_121_, 5);
v_proofIrrelevance_128_ = lean_ctor_get_uint8(v___x_121_, 6);
v_assignSyntheticOpaque_129_ = lean_ctor_get_uint8(v___x_121_, 7);
v_offsetCnstrs_130_ = lean_ctor_get_uint8(v___x_121_, 8);
v_etaStruct_131_ = lean_ctor_get_uint8(v___x_121_, 10);
v_univApprox_132_ = lean_ctor_get_uint8(v___x_121_, 11);
v_iota_133_ = lean_ctor_get_uint8(v___x_121_, 12);
v_beta_134_ = lean_ctor_get_uint8(v___x_121_, 13);
v_proj_135_ = lean_ctor_get_uint8(v___x_121_, 14);
v_zeta_136_ = lean_ctor_get_uint8(v___x_121_, 15);
v_zetaDelta_137_ = lean_ctor_get_uint8(v___x_121_, 16);
v_zetaUnused_138_ = lean_ctor_get_uint8(v___x_121_, 17);
v_zetaHave_139_ = lean_ctor_get_uint8(v___x_121_, 18);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_176_ == 0)
{
v___x_141_ = v___x_121_;
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
else
{
lean_dec(v___x_121_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
uint8_t v_trackZetaDelta_143_; lean_object* v_zetaDeltaSet_144_; lean_object* v_lctx_145_; lean_object* v_localInstances_146_; lean_object* v_defEqCtx_x3f_147_; lean_object* v_synthPendingDepth_148_; lean_object* v_canUnfold_x3f_149_; uint8_t v_univApprox_150_; uint8_t v_inTypeClassResolution_151_; uint8_t v_cacheInferType_152_; uint8_t v___x_153_; lean_object* v_config_155_; 
v_trackZetaDelta_143_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7);
v_zetaDeltaSet_144_ = lean_ctor_get(v_a_115_, 1);
v_lctx_145_ = lean_ctor_get(v_a_115_, 2);
v_localInstances_146_ = lean_ctor_get(v_a_115_, 3);
v_defEqCtx_x3f_147_ = lean_ctor_get(v_a_115_, 4);
v_synthPendingDepth_148_ = lean_ctor_get(v_a_115_, 5);
v_canUnfold_x3f_149_ = lean_ctor_get(v_a_115_, 6);
v_univApprox_150_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_151_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 2);
v_cacheInferType_152_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 3);
v___x_153_ = 1;
if (v_isShared_142_ == 0)
{
v_config_155_ = v___x_141_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 0, v_foApprox_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 1, v_ctxApprox_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 2, v_quasiPatternApprox_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 3, v_constApprox_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 4, v_isDefEqStuckEx_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 5, v_unificationHints_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 6, v_proofIrrelevance_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 7, v_assignSyntheticOpaque_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 8, v_offsetCnstrs_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 10, v_etaStruct_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 11, v_univApprox_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 12, v_iota_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 13, v_beta_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 14, v_proj_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 15, v_zeta_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 16, v_zetaDelta_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 17, v_zetaUnused_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, 18, v_zetaHave_139_);
v_config_155_ = v_reuseFailAlloc_175_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v_key_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_ctor_set_uint8(v_config_155_, 9, v___x_153_);
v___x_156_ = l_Lean_Meta_Context_configKey(v_a_115_);
v___x_157_ = 3ULL;
v___x_158_ = lean_uint64_shift_right(v___x_156_, v___x_157_);
v___x_159_ = lean_uint64_shift_left(v___x_158_, v___x_157_);
v___x_160_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
v_key_161_ = lean_uint64_lor(v___x_159_, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_162_, 0, v_config_155_);
lean_ctor_set_uint64(v___x_162_, sizeof(void*)*1, v_key_161_);
lean_inc(v_canUnfold_x3f_149_);
lean_inc(v_synthPendingDepth_148_);
lean_inc(v_defEqCtx_x3f_147_);
lean_inc_ref(v_localInstances_146_);
lean_inc_ref(v_lctx_145_);
lean_inc(v_zetaDeltaSet_144_);
v___x_163_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_zetaDeltaSet_144_);
lean_ctor_set(v___x_163_, 2, v_lctx_145_);
lean_ctor_set(v___x_163_, 3, v_localInstances_146_);
lean_ctor_set(v___x_163_, 4, v_defEqCtx_x3f_147_);
lean_ctor_set(v___x_163_, 5, v_synthPendingDepth_148_);
lean_ctor_set(v___x_163_, 6, v_canUnfold_x3f_149_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7, v_trackZetaDelta_143_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 1, v_univApprox_150_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 2, v_inTypeClassResolution_151_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 3, v_cacheInferType_152_);
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc(v_a_116_);
lean_inc_ref(v___x_163_);
v___x_164_ = lean_infer_type(v_self_120_, v___x_163_, v_a_116_, v_a_117_, v_a_118_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = l_Lean_Meta_isExprDefEq(v_a_165_, v_type_113_, v___x_163_, v_a_116_, v_a_117_, v_a_118_);
lean_dec_ref_known(v___x_163_, 7);
return v___x_166_;
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref_known(v___x_163_, 7);
lean_dec_ref(v_type_113_);
v_a_167_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_164_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_177_, lean_object* v_n_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_177_, v_n_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_196_){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = l_Lean_Expr_cleanupAnnotations(v_e_196_);
v___x_198_ = l_Lean_Expr_isApp(v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v___x_197_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v_arg_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_arg_200_ = lean_ctor_get(v___x_197_, 1);
lean_inc_ref(v_arg_200_);
v___x_201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_197_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_200_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_arg_200_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_209_ = l_Lean_Expr_isConstOf(v___x_207_, v___x_208_);
lean_dec_ref(v___x_207_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_arg_200_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_arg_200_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Rat_ofInt(v_a_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_nat_to_int(v_a_214_);
v___x_216_ = l_Rat_ofInt(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_key_220_; lean_object* v_value_221_; lean_object* v_tail_222_; uint8_t v___x_223_; 
v_key_220_ = lean_ctor_get(v_x_218_, 0);
v_value_221_ = lean_ctor_get(v_x_218_, 1);
v_tail_222_ = lean_ctor_get(v_x_218_, 2);
v___x_223_ = lean_expr_eqv(v_key_220_, v_a_217_);
if (v___x_223_ == 0)
{
v_x_218_ = v_tail_222_;
goto _start;
}
else
{
lean_object* v___x_225_; 
lean_inc(v_value_221_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_value_221_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_226_, v_x_227_);
lean_dec(v_x_227_);
lean_dec_ref(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_buckets_231_; lean_object* v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_buckets_231_ = lean_ctor_get(v_m_229_, 1);
v___x_232_ = lean_array_get_size(v_buckets_231_);
v___x_233_ = l_Lean_Expr_hash(v_a_230_);
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___x_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___x_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_232_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_buckets_231_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_230_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_247_, v_a_248_);
lean_dec_ref(v_a_248_);
lean_dec_ref(v_m_247_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_289_, lean_object* v_model_290_, lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_290_, v_e_291_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v___x_298_; 
lean_dec_ref(v_e_291_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
lean_dec(v___x_297_);
v___x_299_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_291_, v_a_293_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_553_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_553_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_553_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_553_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = l_Lean_Expr_cleanupAnnotations(v_a_300_);
v___x_310_ = l_Lean_Expr_isApp(v___x_309_);
if (v___x_310_ == 0)
{
lean_dec_ref(v___x_309_);
goto v___jp_304_;
}
else
{
lean_object* v_arg_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_arg_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc_ref(v_arg_311_);
v___x_312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_309_);
v___x_313_ = l_Lean_Expr_isApp(v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v___x_312_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
lean_object* v_arg_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_arg_314_ = lean_ctor_get(v___x_312_, 1);
lean_inc_ref(v_arg_314_);
v___x_315_ = l_Lean_Expr_appFnCleanup___redArg(v___x_312_);
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_317_ = l_Lean_Expr_isConstOf(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_Expr_isApp(v___x_315_);
if (v___x_318_ == 0)
{
lean_dec_ref(v___x_315_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
lean_object* v_arg_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_arg_319_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_arg_319_);
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_315_);
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_323_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_327_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_327_ == 0)
{
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_329_ = l_Lean_Expr_isApp(v___x_328_);
if (v___x_329_ == 0)
{
lean_dec_ref(v___x_328_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_328_);
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_337_);
lean_dec_ref(v___x_330_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
goto v___jp_304_;
}
else
{
uint8_t v___x_339_; 
lean_del_object(v___x_302_);
v___x_339_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_289_, v_arg_319_);
lean_dec_ref(v_arg_319_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
if (lean_obj_tag(v_a_343_) == 0)
{
lean_dec_ref(v_arg_311_);
return v___x_342_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_345_; 
lean_dec_ref_known(v___x_342_, 1);
v_val_344_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v_a_343_, 1);
v___x_345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
if (lean_obj_tag(v_a_346_) == 0)
{
lean_dec(v_val_344_);
return v___x_345_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_362_; 
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v___x_345_, 0);
lean_dec(v_unused_363_);
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_362_;
goto v_resetjp_347_;
}
else
{
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_362_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_val_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_361_; 
v_val_350_ = lean_ctor_get(v_a_346_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_361_ == 0)
{
v___x_352_ = v_a_346_;
v_isShared_353_ = v_isSharedCheck_361_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_val_350_);
lean_dec(v_a_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_361_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Rat_add(v_val_344_, v_val_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_356_);
v___x_358_ = v___x_348_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
else
{
lean_dec(v_val_344_);
return v___x_345_;
}
}
}
else
{
lean_dec_ref(v_arg_311_);
return v___x_342_;
}
}
}
}
else
{
uint8_t v___x_364_; 
lean_dec_ref(v___x_330_);
lean_del_object(v___x_302_);
v___x_364_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_289_, v_arg_319_);
lean_dec_ref(v_arg_319_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
if (lean_obj_tag(v_a_368_) == 0)
{
lean_dec_ref(v_arg_311_);
return v___x_367_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; 
lean_dec_ref_known(v___x_367_, 1);
v_val_369_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_a_368_, 1);
v___x_370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
if (lean_obj_tag(v_a_371_) == 0)
{
lean_dec(v_val_369_);
return v___x_370_;
}
else
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_388_);
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
else
{
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_386_; 
v_val_375_ = lean_ctor_get(v_a_371_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_371_);
if (v_isSharedCheck_386_ == 0)
{
v___x_377_ = v_a_371_;
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v_a_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_Rat_sub(v_val_369_, v_val_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_381_);
v___x_383_ = v___x_373_;
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
}
}
}
}
else
{
lean_dec(v_val_369_);
return v___x_370_;
}
}
}
else
{
lean_dec_ref(v_arg_311_);
return v___x_367_;
}
}
}
}
else
{
uint8_t v___x_389_; 
lean_dec_ref(v___x_330_);
lean_del_object(v___x_302_);
v___x_389_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_289_, v_arg_319_);
lean_dec_ref(v_arg_319_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
if (lean_obj_tag(v_a_393_) == 0)
{
lean_dec_ref(v_arg_311_);
return v___x_392_;
}
else
{
lean_object* v_val_394_; lean_object* v___x_395_; 
lean_dec_ref_known(v___x_392_, 1);
v_val_394_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v_a_393_, 1);
v___x_395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
if (lean_obj_tag(v_a_396_) == 0)
{
lean_dec(v_val_394_);
return v___x_395_;
}
else
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_412_; 
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_395_, 0);
lean_dec(v_unused_413_);
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
else
{
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_val_400_ = lean_ctor_get(v_a_396_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_a_396_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v_a_396_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v_a_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Rat_mul(v_val_394_, v_val_400_);
lean_dec(v_val_394_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_406_);
v___x_408_ = v___x_398_;
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
}
}
}
}
else
{
lean_dec(v_val_394_);
return v___x_395_;
}
}
}
else
{
lean_dec_ref(v_arg_311_);
return v___x_392_;
}
}
}
}
else
{
uint8_t v___x_414_; 
lean_dec_ref(v___x_330_);
lean_del_object(v___x_302_);
v___x_414_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_289_, v_arg_319_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_289_, v_arg_319_);
lean_dec_ref(v_arg_319_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v_arg_314_);
lean_dec_ref(v_arg_311_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_getNatValue_x3f(v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_314_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_448_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_448_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
if (lean_obj_tag(v_a_419_) == 0)
{
lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec_ref(v_arg_311_);
v___x_423_ = lean_box(0);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v_val_427_; lean_object* v___x_428_; 
lean_del_object(v___x_421_);
v_val_427_ = lean_ctor_get(v_a_419_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_a_419_, 1);
v___x_428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
if (lean_obj_tag(v_a_429_) == 0)
{
lean_dec(v_val_427_);
return v___x_428_;
}
else
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_446_; 
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_447_);
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v_val_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_445_; 
v_val_433_ = lean_ctor_get(v_a_429_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_445_ == 0)
{
v___x_435_ = v_a_429_;
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_val_433_);
lean_dec(v_a_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_427_);
v___x_438_ = l_Rat_mul(v___x_437_, v_val_433_);
lean_dec_ref(v___x_437_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_440_);
v___x_442_ = v___x_431_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
else
{
lean_dec(v_val_427_);
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_arg_311_);
v_a_449_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_418_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_418_);
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
lean_object* v___x_457_; 
lean_dec_ref(v_arg_319_);
v___x_457_ = l_Lean_Meta_getIntValue_x3f(v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_487_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_487_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_487_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_487_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
if (lean_obj_tag(v_a_458_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec_ref(v_arg_311_);
v___x_462_ = lean_box(0);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
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
else
{
lean_object* v_val_466_; lean_object* v___x_467_; 
lean_del_object(v___x_460_);
v_val_466_ = lean_ctor_get(v_a_458_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v_a_458_, 1);
v___x_467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
if (lean_obj_tag(v_a_468_) == 0)
{
lean_dec(v_val_466_);
return v___x_467_;
}
else
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___x_467_, 0);
lean_dec(v_unused_486_);
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_485_;
goto v_resetjp_469_;
}
else
{
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_485_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_484_; 
v_val_472_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_484_ == 0)
{
v___x_474_ = v_a_468_;
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v_a_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = l_Rat_ofInt(v_val_466_);
v___x_477_ = l_Rat_mul(v___x_476_, v_val_472_);
lean_dec_ref(v___x_476_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_479_);
v___x_481_ = v___x_470_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_dec(v_val_466_);
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_arg_311_);
v_a_488_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_457_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_457_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
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
}
}
}
else
{
uint8_t v___x_496_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_319_);
lean_del_object(v___x_302_);
v___x_496_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_289_, v_arg_314_);
lean_dec_ref(v_arg_314_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_arg_311_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_289_, v_model_290_, v_arg_311_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
if (lean_obj_tag(v_a_500_) == 0)
{
return v___x_499_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_499_, 0);
lean_dec(v_unused_517_);
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
else
{
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_516_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v_val_504_ = lean_ctor_get(v_a_500_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_500_);
if (v_isSharedCheck_515_ == 0)
{
v___x_506_ = v_a_500_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v_a_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l_Rat_neg(v_val_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
else
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_518_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_319_);
lean_dec_ref(v_arg_311_);
lean_del_object(v___x_302_);
v___x_518_ = l_Lean_Meta_getNatValue_x3f(v_arg_314_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_arg_314_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_539_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_539_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
if (lean_obj_tag(v_a_519_) == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_538_; 
v_val_527_ = lean_ctor_get(v_a_519_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_519_);
if (v_isSharedCheck_538_ == 0)
{
v___x_529_ = v_a_519_;
v_isShared_530_ = v_isSharedCheck_538_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v_a_519_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_538_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_533_);
v___x_535_ = v___x_521_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_518_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_518_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
else
{
uint8_t v___x_548_; 
lean_dec_ref(v___x_315_);
lean_dec_ref(v_arg_314_);
lean_del_object(v___x_302_);
v___x_548_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_289_, v_arg_311_);
lean_dec_ref(v_arg_311_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
}
v___jp_304_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_299_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_299_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_562_, lean_object* v_model_563_, lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_562_, v_model_563_, v_e_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_model_563_);
lean_dec_ref(v_s_562_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_572_, v_a_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_575_, lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_575_, v_m_576_, v_a_577_);
lean_dec_ref(v_a_577_);
lean_dec_ref(v_m_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_nat_to_int(v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_581_, lean_object* v_a_582_, lean_object* v_x_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_582_, v_x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_585_, lean_object* v_a_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_585_, v_a_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec_ref(v_a_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_589_, lean_object* v_s_590_, lean_object* v_model_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_590_, v_model_591_, v_e_589_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_598_, lean_object* v_s_599_, lean_object* v_model_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_598_, v_s_599_, v_model_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec_ref(v_model_600_);
lean_dec_ref(v_s_599_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
else
{
lean_object* v_key_610_; lean_object* v_tail_611_; uint8_t v___x_612_; 
v_key_610_ = lean_ctor_get(v_x_608_, 0);
v_tail_611_ = lean_ctor_get(v_x_608_, 2);
v___x_612_ = lean_expr_eqv(v_key_610_, v_a_607_);
if (v___x_612_ == 0)
{
v_x_608_ = v_tail_611_;
goto _start;
}
else
{
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_614_, lean_object* v_x_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec_ref(v_a_614_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_buckets_620_; lean_object* v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; uint64_t v___x_624_; uint64_t v_fold_625_; uint64_t v___x_626_; uint64_t v___x_627_; uint64_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_buckets_620_ = lean_ctor_get(v_m_618_, 1);
v___x_621_ = lean_array_get_size(v_buckets_620_);
v___x_622_ = l_Lean_Expr_hash(v_a_619_);
v___x_623_ = 32ULL;
v___x_624_ = lean_uint64_shift_right(v___x_622_, v___x_623_);
v_fold_625_ = lean_uint64_xor(v___x_622_, v___x_624_);
v___x_626_ = 16ULL;
v___x_627_ = lean_uint64_shift_right(v_fold_625_, v___x_626_);
v___x_628_ = lean_uint64_xor(v_fold_625_, v___x_627_);
v___x_629_ = lean_uint64_to_usize(v___x_628_);
v___x_630_ = lean_usize_of_nat(v___x_621_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_sub(v___x_630_, v___x_631_);
v___x_633_ = lean_usize_land(v___x_629_, v___x_632_);
v___x_634_ = lean_array_uget_borrowed(v_buckets_620_, v___x_633_);
v___x_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_619_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_636_, lean_object* v_a_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_636_, v_a_637_);
lean_dec_ref(v_a_637_);
lean_dec_ref(v_m_636_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v___x_640_, lean_object* v_goal_641_, lean_object* v_structId_642_, lean_object* v_as_643_, size_t v_sz_644_, size_t v_i_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = lean_usize_dec_lt(v_i_645_, v_sz_644_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_646_);
return v___x_653_;
}
else
{
lean_object* v_snd_654_; lean_object* v_a_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_687_; 
v_snd_654_ = lean_ctor_get(v_b_646_, 1);
lean_inc(v_snd_654_);
lean_dec_ref(v_b_646_);
v_a_655_ = lean_array_uget(v_as_643_, v_i_645_);
v_fst_656_ = lean_ctor_get(v_a_655_, 0);
v_snd_657_ = lean_ctor_get(v_a_655_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_655_);
if (v_isSharedCheck_687_ == 0)
{
v___x_659_ = v_a_655_;
v_isShared_660_ = v_isSharedCheck_687_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v_a_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_687_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_a_663_; uint8_t v___y_671_; uint8_t v___x_684_; 
v___x_661_ = lean_box(0);
v___x_684_ = lean_nat_dec_eq(v_structId_642_, v_snd_657_);
lean_dec(v_snd_657_);
if (v___x_684_ == 0)
{
v___y_671_ = v___x_684_;
goto v___jp_670_;
}
else
{
uint8_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_654_, v_fst_656_);
v___x_686_ = lean_bool_not(v___x_685_);
v___y_671_ = v___x_686_;
goto v___jp_670_;
}
v___jp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_a_663_);
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_a_663_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
size_t v___x_666_; size_t v___x_667_; 
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_645_, v___x_666_);
v_i_645_ = v___x_667_;
v_b_646_ = v___x_665_;
goto _start;
}
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_dec(v_fst_656_);
v_a_663_ = v_snd_654_;
goto v___jp_662_;
}
else
{
lean_object* v___x_672_; 
lean_inc(v_fst_656_);
v___x_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_640_, v_snd_654_, v_fst_656_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_675_; 
v_val_674_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_a_673_, 1);
v___x_675_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_641_, v_fst_656_, v_val_674_, v_snd_654_);
v_a_663_ = v___x_675_;
goto v___jp_662_;
}
else
{
lean_dec(v_a_673_);
lean_dec(v_fst_656_);
v_a_663_ = v_snd_654_;
goto v___jp_662_;
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_del_object(v___x_659_);
lean_dec(v_fst_656_);
lean_dec(v_snd_654_);
v_a_676_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_672_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_672_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v___x_688_, lean_object* v_goal_689_, lean_object* v_structId_690_, lean_object* v_as_691_, lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_b_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
size_t v_sz_boxed_700_; size_t v_i_boxed_701_; lean_object* v_res_702_; 
v_sz_boxed_700_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_701_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_688_, v_goal_689_, v_structId_690_, v_as_691_, v_sz_boxed_700_, v_i_boxed_701_, v_b_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v_as_691_);
lean_dec(v_structId_690_);
lean_dec_ref(v_goal_689_);
lean_dec_ref(v___x_688_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v___x_703_, lean_object* v_goal_704_, lean_object* v_structId_705_, lean_object* v_as_706_, size_t v_sz_707_, size_t v_i_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_b_709_);
return v___x_716_;
}
else
{
lean_object* v_snd_717_; lean_object* v_a_718_; lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_750_; 
v_snd_717_ = lean_ctor_get(v_b_709_, 1);
lean_inc(v_snd_717_);
lean_dec_ref(v_b_709_);
v_a_718_ = lean_array_uget(v_as_706_, v_i_708_);
v_fst_719_ = lean_ctor_get(v_a_718_, 0);
v_snd_720_ = lean_ctor_get(v_a_718_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_a_718_);
if (v_isSharedCheck_750_ == 0)
{
v___x_722_ = v_a_718_;
v_isShared_723_ = v_isSharedCheck_750_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_dec(v_a_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_750_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v_a_726_; uint8_t v___y_734_; uint8_t v___x_747_; 
v___x_724_ = lean_box(0);
v___x_747_ = lean_nat_dec_eq(v_structId_705_, v_snd_720_);
lean_dec(v_snd_720_);
if (v___x_747_ == 0)
{
v___y_734_ = v___x_747_;
goto v___jp_733_;
}
else
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_717_, v_fst_719_);
v___x_749_ = lean_bool_not(v___x_748_);
v___y_734_ = v___x_749_;
goto v___jp_733_;
}
v___jp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_a_726_);
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_a_726_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_708_, v___x_729_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_703_, v_goal_704_, v_structId_705_, v_as_706_, v_sz_707_, v___x_730_, v___x_728_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_731_;
}
}
v___jp_733_:
{
if (v___y_734_ == 0)
{
lean_dec(v_fst_719_);
v_a_726_ = v_snd_717_;
goto v___jp_725_;
}
else
{
lean_object* v___x_735_; 
lean_inc(v_fst_719_);
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_703_, v_snd_717_, v_fst_719_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
if (lean_obj_tag(v_a_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; 
v_val_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v_a_736_, 1);
v___x_738_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_704_, v_fst_719_, v_val_737_, v_snd_717_);
v_a_726_ = v___x_738_;
goto v___jp_725_;
}
else
{
lean_dec(v_a_736_);
lean_dec(v_fst_719_);
v_a_726_ = v_snd_717_;
goto v___jp_725_;
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_del_object(v___x_722_);
lean_dec(v_fst_719_);
lean_dec(v_snd_717_);
v_a_739_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_735_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v___x_751_, lean_object* v_goal_752_, lean_object* v_structId_753_, lean_object* v_as_754_, lean_object* v_sz_755_, lean_object* v_i_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_755_);
lean_dec(v_sz_755_);
v_i_boxed_764_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_751_, v_goal_752_, v_structId_753_, v_as_754_, v_sz_boxed_763_, v_i_boxed_764_, v_b_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec_ref(v_as_754_);
lean_dec(v_structId_753_);
lean_dec_ref(v_goal_752_);
lean_dec_ref(v___x_751_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_766_, lean_object* v___x_767_, lean_object* v_goal_768_, lean_object* v_structId_769_, lean_object* v_n_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
if (lean_obj_tag(v_n_770_) == 0)
{
lean_object* v_cs_777_; lean_object* v___x_778_; lean_object* v___x_779_; size_t v_sz_780_; size_t v___x_781_; lean_object* v___x_782_; 
v_cs_777_ = lean_ctor_get(v_n_770_, 0);
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_b_771_);
v_sz_780_ = lean_array_size(v_cs_777_);
v___x_781_ = ((size_t)0ULL);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_766_, v___x_767_, v_goal_768_, v_structId_769_, v_cs_777_, v_sz_780_, v___x_781_, v___x_779_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_797_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
if (lean_obj_tag(v_fst_787_) == 0)
{
lean_object* v_snd_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_snd_788_ = lean_ctor_get(v_a_783_, 1);
lean_inc(v_snd_788_);
lean_dec(v_a_783_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_snd_788_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; 
lean_inc_ref(v_fst_787_);
lean_dec(v_a_783_);
v_val_793_ = lean_ctor_get(v_fst_787_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_fst_787_, 1);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_val_793_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_val_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_782_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_782_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_vs_806_; lean_object* v___x_807_; lean_object* v___x_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_vs_806_ = lean_ctor_get(v_n_770_, 0);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_b_771_);
v_sz_809_ = lean_array_size(v_vs_806_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_767_, v_goal_768_, v_structId_769_, v_vs_806_, v_sz_809_, v___x_810_, v___x_808_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_826_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_826_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_826_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_826_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_fst_816_; 
v_fst_816_ = lean_ctor_get(v_a_812_, 0);
if (lean_obj_tag(v_fst_816_) == 0)
{
lean_object* v_snd_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_snd_817_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_snd_817_);
lean_dec(v_a_812_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_snd_817_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_818_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; 
lean_inc_ref(v_fst_816_);
lean_dec(v_a_812_);
v_val_822_ = lean_ctor_get(v_fst_816_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_fst_816_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_val_822_);
v___x_824_ = v___x_814_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_val_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_811_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_811_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_835_, lean_object* v___x_836_, lean_object* v_goal_837_, lean_object* v_structId_838_, lean_object* v_as_839_, size_t v_sz_840_, size_t v_i_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_841_, v_sz_840_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v_b_842_);
return v___x_849_;
}
else
{
lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_884_; 
v_snd_850_ = lean_ctor_get(v_b_842_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_b_842_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_b_842_, 0);
lean_dec(v_unused_885_);
v___x_852_ = v_b_842_;
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_dec(v_b_842_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_array_uget_borrowed(v_as_839_, v_i_841_);
lean_inc(v_snd_850_);
v___x_855_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_835_, v___x_836_, v_goal_837_, v_structId_838_, v_a_854_, v_snd_850_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_875_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_875_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_a_856_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_860_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_snd_850_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
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
}
else
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_del_object(v___x_858_);
lean_dec(v_snd_850_);
v_a_867_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v_a_856_, 1);
v___x_868_ = lean_box(0);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_a_867_);
lean_ctor_set(v___x_852_, 0, v___x_868_);
v___x_870_ = v___x_852_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_867_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
size_t v___x_871_; size_t v___x_872_; 
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_841_, v___x_871_);
v_i_841_ = v___x_872_;
v_b_842_ = v___x_870_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
v_a_876_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_855_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_855_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_886_, lean_object* v___x_887_, lean_object* v_goal_888_, lean_object* v_structId_889_, lean_object* v_as_890_, lean_object* v_sz_891_, lean_object* v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_891_);
lean_dec(v_sz_891_);
v_i_boxed_900_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_886_, v___x_887_, v_goal_888_, v_structId_889_, v_as_890_, v_sz_boxed_899_, v_i_boxed_900_, v_b_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_as_890_);
lean_dec(v_structId_889_);
lean_dec_ref(v_goal_888_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v_init_886_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_902_, lean_object* v___x_903_, lean_object* v_goal_904_, lean_object* v_structId_905_, lean_object* v_n_906_, lean_object* v_b_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_902_, v___x_903_, v_goal_904_, v_structId_905_, v_n_906_, v_b_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_n_906_);
lean_dec(v_structId_905_);
lean_dec_ref(v_goal_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v_init_902_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v___x_914_, lean_object* v_goal_915_, lean_object* v_structId_916_, lean_object* v_as_917_, size_t v_sz_918_, size_t v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_b_920_);
return v___x_927_;
}
else
{
lean_object* v_snd_928_; lean_object* v_a_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_961_; 
v_snd_928_ = lean_ctor_get(v_b_920_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v_b_920_);
v_a_929_ = lean_array_uget(v_as_917_, v_i_919_);
v_fst_930_ = lean_ctor_get(v_a_929_, 0);
v_snd_931_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_961_ == 0)
{
v___x_933_ = v_a_929_;
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v_a_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v_a_937_; uint8_t v___y_945_; uint8_t v___x_958_; 
v___x_935_ = lean_box(0);
v___x_958_ = lean_nat_dec_eq(v_structId_916_, v_snd_931_);
lean_dec(v_snd_931_);
if (v___x_958_ == 0)
{
v___y_945_ = v___x_958_;
goto v___jp_944_;
}
else
{
uint8_t v___x_959_; uint8_t v___x_960_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_928_, v_fst_930_);
v___x_960_ = lean_bool_not(v___x_959_);
v___y_945_ = v___x_960_;
goto v___jp_944_;
}
v___jp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_a_937_);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_939_ = v___x_933_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_a_937_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
size_t v___x_940_; size_t v___x_941_; 
v___x_940_ = ((size_t)1ULL);
v___x_941_ = lean_usize_add(v_i_919_, v___x_940_);
v_i_919_ = v___x_941_;
v_b_920_ = v___x_939_;
goto _start;
}
}
v___jp_944_:
{
if (v___y_945_ == 0)
{
lean_dec(v_fst_930_);
v_a_937_ = v_snd_928_;
goto v___jp_936_;
}
else
{
lean_object* v___x_946_; 
lean_inc(v_fst_930_);
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_914_, v_snd_928_, v_fst_930_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
if (lean_obj_tag(v_a_947_) == 1)
{
lean_object* v_val_948_; lean_object* v___x_949_; 
v_val_948_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_a_947_, 1);
v___x_949_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_915_, v_fst_930_, v_val_948_, v_snd_928_);
v_a_937_ = v___x_949_;
goto v___jp_936_;
}
else
{
lean_dec(v_a_947_);
lean_dec(v_fst_930_);
v_a_937_ = v_snd_928_;
goto v___jp_936_;
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_933_);
lean_dec(v_fst_930_);
lean_dec(v_snd_928_);
v_a_950_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_946_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v___x_962_, lean_object* v_goal_963_, lean_object* v_structId_964_, lean_object* v_as_965_, lean_object* v_sz_966_, lean_object* v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_975_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_962_, v_goal_963_, v_structId_964_, v_as_965_, v_sz_boxed_974_, v_i_boxed_975_, v_b_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_as_965_);
lean_dec(v_structId_964_);
lean_dec_ref(v_goal_963_);
lean_dec_ref(v___x_962_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v___x_977_, lean_object* v_goal_978_, lean_object* v_structId_979_, lean_object* v_as_980_, size_t v_sz_981_, size_t v_i_982_, lean_object* v_b_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = lean_usize_dec_lt(v_i_982_, v_sz_981_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_b_983_);
return v___x_990_;
}
else
{
lean_object* v_snd_991_; lean_object* v_a_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1024_; 
v_snd_991_ = lean_ctor_get(v_b_983_, 1);
lean_inc(v_snd_991_);
lean_dec_ref(v_b_983_);
v_a_992_ = lean_array_uget(v_as_980_, v_i_982_);
v_fst_993_ = lean_ctor_get(v_a_992_, 0);
v_snd_994_ = lean_ctor_get(v_a_992_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_992_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_996_ = v_a_992_;
v_isShared_997_ = v_isSharedCheck_1024_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v_a_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1024_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v_a_1000_; uint8_t v___y_1008_; uint8_t v___x_1021_; 
v___x_998_ = lean_box(0);
v___x_1021_ = lean_nat_dec_eq(v_structId_979_, v_snd_994_);
lean_dec(v_snd_994_);
if (v___x_1021_ == 0)
{
v___y_1008_ = v___x_1021_;
goto v___jp_1007_;
}
else
{
uint8_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_991_, v_fst_993_);
v___x_1023_ = lean_bool_not(v___x_1022_);
v___y_1008_ = v___x_1023_;
goto v___jp_1007_;
}
v___jp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v_a_1000_);
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_a_1000_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_982_, v___x_1003_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_977_, v_goal_978_, v_structId_979_, v_as_980_, v_sz_981_, v___x_1004_, v___x_1002_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_1005_;
}
}
v___jp_1007_:
{
if (v___y_1008_ == 0)
{
lean_dec(v_fst_993_);
v_a_1000_ = v_snd_991_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1009_; 
lean_inc(v_fst_993_);
v___x_1009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_977_, v_snd_991_, v_fst_993_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
if (lean_obj_tag(v_a_1010_) == 1)
{
lean_object* v_val_1011_; lean_object* v___x_1012_; 
v_val_1011_ = lean_ctor_get(v_a_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v_a_1010_, 1);
v___x_1012_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_978_, v_fst_993_, v_val_1011_, v_snd_991_);
v_a_1000_ = v___x_1012_;
goto v___jp_999_;
}
else
{
lean_dec(v_a_1010_);
lean_dec(v_fst_993_);
v_a_1000_ = v_snd_991_;
goto v___jp_999_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_996_);
lean_dec(v_fst_993_);
lean_dec(v_snd_991_);
v_a_1013_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1009_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1009_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v___x_1025_, lean_object* v_goal_1026_, lean_object* v_structId_1027_, lean_object* v_as_1028_, lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1025_, v_goal_1026_, v_structId_1027_, v_as_1028_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1028_);
lean_dec(v_structId_1027_);
lean_dec_ref(v_goal_1026_);
lean_dec_ref(v___x_1025_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1040_, lean_object* v_goal_1041_, lean_object* v_structId_1042_, lean_object* v_t_1043_, lean_object* v_init_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_root_1050_; lean_object* v_tail_1051_; lean_object* v___x_1052_; 
v_root_1050_ = lean_ctor_get(v_t_1043_, 0);
v_tail_1051_ = lean_ctor_get(v_t_1043_, 1);
lean_inc_ref(v_init_1044_);
v___x_1052_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1044_, v___x_1040_, v_goal_1041_, v_structId_1042_, v_root_1050_, v_init_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
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
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1040_, v_goal_1041_, v_structId_1042_, v_tail_1051_, v_sz_1064_, v___x_1065_, v___x_1063_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1098_, lean_object* v_goal_1099_, lean_object* v_structId_1100_, lean_object* v_t_1101_, lean_object* v_init_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1098_, v_goal_1099_, v_structId_1100_, v_t_1101_, v_init_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v_t_1101_);
lean_dec(v_structId_1100_);
lean_dec_ref(v_goal_1099_);
lean_dec_ref(v___x_1098_);
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
v___x_1124_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1123_, v_goal_1109_, v_structId_1110_, v_exprToStructIdEntries_1121_, v_model_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
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
v_ref_1129_ = lean_ctor_get(v_a_1114_, 5);
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
v_ref_2178_ = lean_ctor_get(v_a_2110_, 5);
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

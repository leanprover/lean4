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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1;
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_20_; size_t v___x_21_; size_t v___x_22_; 
v___x_20_ = ((size_t)5ULL);
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_shift_left(v___x_21_, v___x_20_);
return v___x_22_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_23_; size_t v___x_24_; size_t v___x_25_; 
v___x_23_ = ((size_t)1ULL);
v___x_24_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0);
v___x_25_ = lean_usize_sub(v___x_24_, v___x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(lean_object* v_x_26_, size_t v_x_27_, lean_object* v_x_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_es_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_50_; 
v_es_29_ = lean_ctor_get(v_x_26_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_26_);
if (v_isSharedCheck_50_ == 0)
{
v___x_31_ = v_x_26_;
v_isShared_32_ = v_isSharedCheck_50_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_es_29_);
lean_dec(v_x_26_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_50_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; lean_object* v_j_37_; lean_object* v___x_38_; 
v___x_33_ = lean_box(2);
v___x_34_ = ((size_t)5ULL);
v___x_35_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1);
v___x_36_ = lean_usize_land(v_x_27_, v___x_35_);
v_j_37_ = lean_usize_to_nat(v___x_36_);
v___x_38_ = lean_array_get(v___x_33_, v_es_29_, v_j_37_);
lean_dec(v_j_37_);
lean_dec_ref(v_es_29_);
switch(lean_obj_tag(v___x_38_))
{
case 0:
{
lean_object* v_key_39_; lean_object* v_val_40_; uint8_t v___x_41_; 
v_key_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_key_39_);
v_val_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_val_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_28_, v_key_39_);
lean_dec(v_key_39_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec(v_val_40_);
lean_del_object(v___x_31_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v___x_44_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 1);
lean_ctor_set(v___x_31_, 0, v_val_40_);
v___x_44_ = v___x_31_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_val_40_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
case 1:
{
lean_object* v_node_46_; size_t v___x_47_; 
lean_del_object(v___x_31_);
v_node_46_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_node_46_);
lean_dec_ref(v___x_38_);
v___x_47_ = lean_usize_shift_right(v_x_27_, v___x_34_);
v_x_26_ = v_node_46_;
v_x_27_ = v___x_47_;
goto _start;
}
default: 
{
lean_object* v___x_49_; 
lean_del_object(v___x_31_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
}
}
else
{
lean_object* v_ks_51_; lean_object* v_vs_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_ks_51_ = lean_ctor_get(v_x_26_, 0);
lean_inc_ref(v_ks_51_);
v_vs_52_ = lean_ctor_get(v_x_26_, 1);
lean_inc_ref(v_vs_52_);
lean_dec_ref(v_x_26_);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_ks_51_, v_vs_52_, v___x_53_, v_x_28_);
lean_dec_ref(v_vs_52_);
lean_dec_ref(v_ks_51_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
size_t v_x_335__boxed_58_; lean_object* v_res_59_; 
v_x_335__boxed_58_ = lean_unbox_usize(v_x_56_);
lean_dec(v_x_56_);
v_res_59_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_55_, v_x_335__boxed_58_, v_x_57_);
lean_dec_ref(v_x_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint64_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; 
v___x_62_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_61_);
v___x_63_ = lean_uint64_to_usize(v___x_62_);
v___x_64_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_60_, v___x_63_, v_x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_65_, v_x_66_);
lean_dec_ref(v_x_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object* v_s_68_, lean_object* v_e_69_){
_start:
{
lean_object* v_varMap_70_; lean_object* v_assignment_71_; lean_object* v___x_72_; 
v_varMap_70_ = lean_ctor_get(v_s_68_, 31);
lean_inc_ref(v_varMap_70_);
v_assignment_71_ = lean_ctor_get(v_s_68_, 35);
lean_inc_ref(v_assignment_71_);
lean_dec_ref(v_s_68_);
v___x_72_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_70_, v_e_69_);
if (lean_obj_tag(v___x_72_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_85_; 
v_val_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_85_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_85_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_85_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v_size_77_; uint8_t v___x_78_; 
v_size_77_ = lean_ctor_get(v_assignment_71_, 2);
v___x_78_ = lean_nat_dec_lt(v_val_73_, v_size_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_del_object(v___x_75_);
lean_dec(v_val_73_);
lean_dec_ref(v_assignment_71_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_80_ = l_instInhabitedRat;
v___x_81_ = l_Lean_PersistentArray_get_x21___redArg(v___x_80_, v_assignment_71_, v_val_73_);
lean_dec(v_val_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_81_);
v___x_83_ = v___x_75_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v___x_72_);
lean_dec_ref(v_assignment_71_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object* v_s_87_, lean_object* v_e_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_87_, v_e_88_);
lean_dec_ref(v_e_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object* v_00_u03b2_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object* v_00_u03b2_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_94_, v_x_95_, v_x_96_);
lean_dec_ref(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object* v_00_u03b2_98_, lean_object* v_x_99_, size_t v_x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_99_, v_x_100_, v_x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
size_t v_x_448__boxed_107_; lean_object* v_res_108_; 
v_x_448__boxed_107_ = lean_unbox_usize(v_x_105_);
lean_dec(v_x_105_);
v_res_108_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_103_, v_x_104_, v_x_448__boxed_107_, v_x_106_);
lean_dec_ref(v_x_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_109_, lean_object* v_keys_110_, lean_object* v_vals_111_, lean_object* v_heq_112_, lean_object* v_i_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_110_, v_vals_111_, v_i_113_, v_k_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_116_, lean_object* v_keys_117_, lean_object* v_vals_118_, lean_object* v_heq_119_, lean_object* v_i_120_, lean_object* v_k_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_116_, v_keys_117_, v_vals_118_, v_heq_119_, v_i_120_, v_k_121_);
lean_dec_ref(v_k_121_);
lean_dec_ref(v_vals_118_);
lean_dec_ref(v_keys_117_);
return v_res_122_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0(void){
_start:
{
uint8_t v___x_123_; uint64_t v___x_124_; 
v___x_123_ = 1;
v___x_124_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_125_, lean_object* v_n_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_self_132_; lean_object* v___x_133_; uint8_t v_foApprox_134_; uint8_t v_ctxApprox_135_; uint8_t v_quasiPatternApprox_136_; uint8_t v_constApprox_137_; uint8_t v_isDefEqStuckEx_138_; uint8_t v_unificationHints_139_; uint8_t v_proofIrrelevance_140_; uint8_t v_assignSyntheticOpaque_141_; uint8_t v_offsetCnstrs_142_; uint8_t v_etaStruct_143_; uint8_t v_univApprox_144_; uint8_t v_iota_145_; uint8_t v_beta_146_; uint8_t v_proj_147_; uint8_t v_zeta_148_; uint8_t v_zetaDelta_149_; uint8_t v_zetaUnused_150_; uint8_t v_zetaHave_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_201_; 
v_self_132_ = lean_ctor_get(v_n_126_, 0);
lean_inc_ref(v_self_132_);
lean_dec_ref(v_n_126_);
v___x_133_ = l_Lean_Meta_Context_config(v_a_127_);
v_foApprox_134_ = lean_ctor_get_uint8(v___x_133_, 0);
v_ctxApprox_135_ = lean_ctor_get_uint8(v___x_133_, 1);
v_quasiPatternApprox_136_ = lean_ctor_get_uint8(v___x_133_, 2);
v_constApprox_137_ = lean_ctor_get_uint8(v___x_133_, 3);
v_isDefEqStuckEx_138_ = lean_ctor_get_uint8(v___x_133_, 4);
v_unificationHints_139_ = lean_ctor_get_uint8(v___x_133_, 5);
v_proofIrrelevance_140_ = lean_ctor_get_uint8(v___x_133_, 6);
v_assignSyntheticOpaque_141_ = lean_ctor_get_uint8(v___x_133_, 7);
v_offsetCnstrs_142_ = lean_ctor_get_uint8(v___x_133_, 8);
v_etaStruct_143_ = lean_ctor_get_uint8(v___x_133_, 10);
v_univApprox_144_ = lean_ctor_get_uint8(v___x_133_, 11);
v_iota_145_ = lean_ctor_get_uint8(v___x_133_, 12);
v_beta_146_ = lean_ctor_get_uint8(v___x_133_, 13);
v_proj_147_ = lean_ctor_get_uint8(v___x_133_, 14);
v_zeta_148_ = lean_ctor_get_uint8(v___x_133_, 15);
v_zetaDelta_149_ = lean_ctor_get_uint8(v___x_133_, 16);
v_zetaUnused_150_ = lean_ctor_get_uint8(v___x_133_, 17);
v_zetaHave_151_ = lean_ctor_get_uint8(v___x_133_, 18);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_201_ == 0)
{
v___x_153_ = v___x_133_;
v_isShared_154_ = v_isSharedCheck_201_;
goto v_resetjp_152_;
}
else
{
lean_dec(v___x_133_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_201_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v_trackZetaDelta_155_; lean_object* v_zetaDeltaSet_156_; lean_object* v_lctx_157_; lean_object* v_localInstances_158_; lean_object* v_defEqCtx_x3f_159_; lean_object* v_synthPendingDepth_160_; lean_object* v_canUnfold_x3f_161_; uint8_t v_univApprox_162_; uint8_t v_inTypeClassResolution_163_; uint8_t v_cacheInferType_164_; uint8_t v___x_165_; lean_object* v_config_167_; 
v_trackZetaDelta_155_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7);
v_zetaDeltaSet_156_ = lean_ctor_get(v_a_127_, 1);
lean_inc(v_zetaDeltaSet_156_);
v_lctx_157_ = lean_ctor_get(v_a_127_, 2);
lean_inc_ref(v_lctx_157_);
v_localInstances_158_ = lean_ctor_get(v_a_127_, 3);
lean_inc_ref(v_localInstances_158_);
v_defEqCtx_x3f_159_ = lean_ctor_get(v_a_127_, 4);
lean_inc(v_defEqCtx_x3f_159_);
v_synthPendingDepth_160_ = lean_ctor_get(v_a_127_, 5);
lean_inc(v_synthPendingDepth_160_);
v_canUnfold_x3f_161_ = lean_ctor_get(v_a_127_, 6);
lean_inc(v_canUnfold_x3f_161_);
v_univApprox_162_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_163_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 2);
v_cacheInferType_164_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 3);
v___x_165_ = 1;
if (v_isShared_154_ == 0)
{
v_config_167_ = v___x_153_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 0, v_foApprox_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 1, v_ctxApprox_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 2, v_quasiPatternApprox_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 3, v_constApprox_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 4, v_isDefEqStuckEx_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 5, v_unificationHints_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 6, v_proofIrrelevance_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 7, v_assignSyntheticOpaque_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 8, v_offsetCnstrs_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 10, v_etaStruct_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 11, v_univApprox_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 12, v_iota_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 13, v_beta_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 14, v_proj_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 15, v_zeta_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 16, v_zetaDelta_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 17, v_zetaUnused_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, 18, v_zetaHave_151_);
v_config_167_ = v_reuseFailAlloc_200_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
uint64_t v___x_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_192_; 
lean_ctor_set_uint8(v_config_167_, 9, v___x_165_);
v___x_168_ = l_Lean_Meta_Context_configKey(v_a_127_);
v_isSharedCheck_192_ = !lean_is_exclusive(v_a_127_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; lean_object* v_unused_197_; lean_object* v_unused_198_; lean_object* v_unused_199_; 
v_unused_193_ = lean_ctor_get(v_a_127_, 6);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_a_127_, 5);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_a_127_, 4);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v_a_127_, 3);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v_a_127_, 2);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_a_127_, 1);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_a_127_, 0);
lean_dec(v_unused_199_);
v___x_170_ = v_a_127_;
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_a_127_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_192_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v_key_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_172_ = 2ULL;
v___x_173_ = lean_uint64_shift_right(v___x_168_, v___x_172_);
v___x_174_ = lean_uint64_shift_left(v___x_173_, v___x_172_);
v___x_175_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
v_key_176_ = lean_uint64_lor(v___x_174_, v___x_175_);
v___x_177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_177_, 0, v_config_167_);
lean_ctor_set_uint64(v___x_177_, sizeof(void*)*1, v_key_176_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_177_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_zetaDeltaSet_156_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_lctx_157_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_localInstances_158_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_defEqCtx_x3f_159_);
lean_ctor_set(v_reuseFailAlloc_191_, 5, v_synthPendingDepth_160_);
lean_ctor_set(v_reuseFailAlloc_191_, 6, v_canUnfold_x3f_161_);
lean_ctor_set_uint8(v_reuseFailAlloc_191_, sizeof(void*)*7, v_trackZetaDelta_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_191_, sizeof(void*)*7 + 1, v_univApprox_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_191_, sizeof(void*)*7 + 2, v_inTypeClassResolution_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_191_, sizeof(void*)*7 + 3, v_cacheInferType_164_);
v___x_179_ = v_reuseFailAlloc_191_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_179_);
v___x_180_ = lean_infer_type(v_self_132_, v___x_179_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_Lean_Meta_isExprDefEq(v_a_181_, v_type_125_, v___x_179_, v_a_128_, v_a_129_, v_a_130_);
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v___x_179_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_type_125_);
v_a_183_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_180_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_180_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_202_, lean_object* v_n_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_202_, v_n_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_221_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = l_Lean_Expr_cleanupAnnotations(v_e_221_);
v___x_223_ = l_Lean_Expr_isApp(v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec_ref(v___x_222_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
lean_object* v_arg_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_arg_225_ = lean_ctor_get(v___x_222_, 1);
lean_inc_ref(v_arg_225_);
v___x_226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_222_);
v___x_227_ = l_Lean_Expr_isApp(v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v_arg_225_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_226_);
v___x_230_ = l_Lean_Expr_isApp(v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec_ref(v___x_229_);
lean_dec_ref(v_arg_225_);
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_229_);
v___x_233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_234_ = l_Lean_Expr_isConstOf(v___x_232_, v___x_233_);
lean_dec_ref(v___x_232_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec_ref(v_arg_225_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_arg_225_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Rat_ofInt(v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_nat_to_int(v_a_239_);
v___x_241_ = l_Rat_ofInt(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v_key_245_; lean_object* v_value_246_; lean_object* v_tail_247_; uint8_t v___x_248_; 
v_key_245_ = lean_ctor_get(v_x_243_, 0);
v_value_246_ = lean_ctor_get(v_x_243_, 1);
v_tail_247_ = lean_ctor_get(v_x_243_, 2);
v___x_248_ = lean_expr_eqv(v_key_245_, v_a_242_);
if (v___x_248_ == 0)
{
v_x_243_ = v_tail_247_;
goto _start;
}
else
{
lean_object* v___x_250_; 
lean_inc(v_value_246_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_value_246_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_251_, v_x_252_);
lean_dec(v_x_252_);
lean_dec_ref(v_a_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_buckets_256_; lean_object* v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; uint64_t v_fold_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_buckets_256_ = lean_ctor_get(v_m_254_, 1);
v___x_257_ = lean_array_get_size(v_buckets_256_);
v___x_258_ = l_Lean_Expr_hash(v_a_255_);
v___x_259_ = 32ULL;
v___x_260_ = lean_uint64_shift_right(v___x_258_, v___x_259_);
v_fold_261_ = lean_uint64_xor(v___x_258_, v___x_260_);
v___x_262_ = 16ULL;
v___x_263_ = lean_uint64_shift_right(v_fold_261_, v___x_262_);
v___x_264_ = lean_uint64_xor(v_fold_261_, v___x_263_);
v___x_265_ = lean_uint64_to_usize(v___x_264_);
v___x_266_ = lean_usize_of_nat(v___x_257_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_sub(v___x_266_, v___x_267_);
v___x_269_ = lean_usize_land(v___x_265_, v___x_268_);
v___x_270_ = lean_array_uget_borrowed(v_buckets_256_, v___x_269_);
v___x_271_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_255_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_272_, v_a_273_);
lean_dec_ref(v_a_273_);
lean_dec_ref(v_m_272_);
return v_res_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_314_, lean_object* v_model_315_, lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_315_, v_e_316_);
if (lean_obj_tag(v___x_322_) == 1)
{
lean_object* v___x_323_; 
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec_ref(v_e_316_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v___x_322_);
v___x_324_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_316_, v_a_318_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_578_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_578_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_578_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_578_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = l_Lean_Expr_cleanupAnnotations(v_a_325_);
v___x_335_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v_arg_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_arg_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc_ref(v_arg_336_);
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_338_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_337_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v_arg_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_arg_339_ = lean_ctor_get(v___x_337_, 1);
lean_inc_ref(v_arg_339_);
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_344_ = lean_ctor_get(v___x_340_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_345_, v___x_348_);
if (v___x_349_ == 0)
{
uint8_t v___x_350_; 
v___x_350_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_350_ == 0)
{
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_352_ = l_Lean_Expr_isApp(v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v___x_351_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_351_);
v___x_354_ = l_Lean_Expr_isApp(v___x_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v___x_353_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_353_);
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_359_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_362_);
lean_dec_ref(v___x_355_);
if (v___x_363_ == 0)
{
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
goto v___jp_329_;
}
else
{
uint8_t v___x_364_; 
lean_del_object(v___x_327_);
v___x_364_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_314_, v_arg_344_);
lean_dec_ref(v_arg_344_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
if (lean_obj_tag(v_a_368_) == 0)
{
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_367_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; 
lean_dec_ref(v___x_367_);
v_val_369_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref(v_a_368_);
v___x_370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
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
v___x_379_ = l_Rat_add(v_val_369_, v_val_375_);
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
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_367_;
}
}
}
}
else
{
uint8_t v___x_389_; 
lean_dec_ref(v___x_355_);
lean_del_object(v___x_327_);
v___x_389_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_314_, v_arg_344_);
lean_dec_ref(v_arg_344_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_392_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
if (lean_obj_tag(v_a_393_) == 0)
{
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_392_;
}
else
{
lean_object* v_val_394_; lean_object* v___x_395_; 
lean_dec_ref(v___x_392_);
v_val_394_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref(v_a_393_);
v___x_395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
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
v___x_404_ = l_Rat_sub(v_val_394_, v_val_400_);
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
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_392_;
}
}
}
}
else
{
uint8_t v___x_414_; 
lean_dec_ref(v___x_355_);
lean_del_object(v___x_327_);
v___x_414_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_314_, v_arg_344_);
lean_dec_ref(v_arg_344_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
if (lean_obj_tag(v_a_418_) == 0)
{
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_417_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_420_; 
lean_dec_ref(v___x_417_);
v_val_419_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref(v_a_418_);
v___x_420_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
if (lean_obj_tag(v_a_421_) == 0)
{
lean_dec(v_val_419_);
return v___x_420_;
}
else
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_437_; 
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_420_, 0);
lean_dec(v_unused_438_);
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
else
{
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_436_; 
v_val_425_ = lean_ctor_get(v_a_421_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_421_);
if (v_isSharedCheck_436_ == 0)
{
v___x_427_ = v_a_421_;
v_isShared_428_ = v_isSharedCheck_436_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v_a_421_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_436_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = l_Rat_mul(v_val_419_, v_val_425_);
lean_dec(v_val_419_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_431_);
v___x_433_ = v___x_423_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
else
{
lean_dec(v_val_419_);
return v___x_420_;
}
}
}
else
{
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v___x_417_;
}
}
}
}
else
{
uint8_t v___x_439_; 
lean_dec_ref(v___x_355_);
lean_del_object(v___x_327_);
v___x_439_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_314_, v_arg_344_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_314_, v_arg_344_);
lean_dec_ref(v_arg_344_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_443_ = l_Lean_Meta_getNatValue_x3f(v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec_ref(v_arg_339_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_473_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_473_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_473_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_473_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
if (lean_obj_tag(v_a_444_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_450_; 
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_448_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; 
lean_del_object(v___x_446_);
v_val_452_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_452_);
lean_dec_ref(v_a_444_);
v___x_453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
if (lean_obj_tag(v_a_454_) == 0)
{
lean_dec(v_val_452_);
return v___x_453_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_471_; 
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v___x_453_, 0);
lean_dec(v_unused_472_);
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_val_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_470_; 
v_val_458_ = lean_ctor_get(v_a_454_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_454_);
if (v_isSharedCheck_470_ == 0)
{
v___x_460_ = v_a_454_;
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_val_458_);
lean_dec(v_a_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_452_);
v___x_463_ = l_Rat_mul(v___x_462_, v_val_458_);
lean_dec_ref(v___x_462_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_465_);
v___x_467_ = v___x_456_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
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
else
{
lean_dec(v_val_452_);
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v_a_474_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_443_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_443_);
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
else
{
lean_object* v___x_482_; 
lean_dec_ref(v_arg_344_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
v___x_482_ = l_Lean_Meta_getIntValue_x3f(v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_512_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_512_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_512_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_512_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
if (lean_obj_tag(v_a_483_) == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_487_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
lean_object* v_val_491_; lean_object* v___x_492_; 
lean_del_object(v___x_485_);
v_val_491_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_val_491_);
lean_dec_ref(v_a_483_);
v___x_492_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
if (lean_obj_tag(v_a_493_) == 0)
{
lean_dec(v_val_491_);
return v___x_492_;
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_510_; 
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v___x_492_, 0);
lean_dec(v_unused_511_);
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_510_;
goto v_resetjp_494_;
}
else
{
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_510_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_509_; 
v_val_497_ = lean_ctor_get(v_a_493_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_499_ = v_a_493_;
v_isShared_500_ = v_isSharedCheck_509_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v_a_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_509_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = l_Rat_ofInt(v_val_491_);
v___x_502_ = l_Rat_mul(v___x_501_, v_val_497_);
lean_dec_ref(v___x_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_504_);
v___x_506_ = v___x_495_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec(v_val_491_);
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v_a_513_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_482_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_482_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
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
uint8_t v___x_521_; 
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
lean_del_object(v___x_327_);
v___x_521_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_314_, v_arg_339_);
lean_dec_ref(v_arg_339_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_arg_336_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_314_, v_model_315_, v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
if (lean_obj_tag(v_a_525_) == 0)
{
return v___x_524_;
}
else
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_541_; 
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v___x_524_, 0);
lean_dec(v_unused_542_);
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_541_;
goto v_resetjp_526_;
}
else
{
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_541_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_540_; 
v_val_529_ = lean_ctor_get(v_a_525_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_540_ == 0)
{
v___x_531_ = v_a_525_;
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v_a_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = l_Rat_neg(v_val_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_535_);
v___x_537_ = v___x_527_;
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
}
}
}
}
else
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_336_);
lean_del_object(v___x_327_);
v___x_543_ = l_Lean_Meta_getNatValue_x3f(v_arg_339_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec_ref(v_arg_339_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_564_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_564_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
if (lean_obj_tag(v_a_544_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_box(0);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v_val_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_563_; 
v_val_552_ = lean_ctor_get(v_a_544_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_544_);
if (v_isSharedCheck_563_ == 0)
{
v___x_554_ = v_a_544_;
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_val_552_);
lean_dec(v_a_544_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_558_);
v___x_560_ = v___x_546_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_543_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_543_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
else
{
uint8_t v___x_573_; 
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_339_);
lean_del_object(v___x_327_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v___x_573_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_314_, v_arg_336_);
lean_dec_ref(v_arg_336_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
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
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
v_a_579_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_324_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_324_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_587_, lean_object* v_model_588_, lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_587_, v_model_588_, v_e_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec_ref(v_model_588_);
lean_dec_ref(v_s_587_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_600_, lean_object* v_m_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_600_, v_m_601_, v_a_602_);
lean_dec_ref(v_a_602_);
lean_dec_ref(v_m_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_nat_to_int(v_a_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_606_, lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_610_, lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_610_, v_a_611_, v_x_612_);
lean_dec(v_x_612_);
lean_dec_ref(v_a_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_614_, lean_object* v_s_615_, lean_object* v_model_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_615_, v_model_616_, v_e_614_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_623_, lean_object* v_s_624_, lean_object* v_model_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_623_, v_s_624_, v_model_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec_ref(v_model_625_);
lean_dec_ref(v_s_624_);
return v_res_631_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
else
{
lean_object* v_key_635_; lean_object* v_tail_636_; uint8_t v___x_637_; 
v_key_635_ = lean_ctor_get(v_x_633_, 0);
v_tail_636_ = lean_ctor_get(v_x_633_, 2);
v___x_637_ = lean_expr_eqv(v_key_635_, v_a_632_);
if (v___x_637_ == 0)
{
v_x_633_ = v_tail_636_;
goto _start;
}
else
{
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec_ref(v_a_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_buckets_645_; lean_object* v___x_646_; uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v_fold_650_; uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_buckets_645_ = lean_ctor_get(v_m_643_, 1);
v___x_646_ = lean_array_get_size(v_buckets_645_);
v___x_647_ = l_Lean_Expr_hash(v_a_644_);
v___x_648_ = 32ULL;
v___x_649_ = lean_uint64_shift_right(v___x_647_, v___x_648_);
v_fold_650_ = lean_uint64_xor(v___x_647_, v___x_649_);
v___x_651_ = 16ULL;
v___x_652_ = lean_uint64_shift_right(v_fold_650_, v___x_651_);
v___x_653_ = lean_uint64_xor(v_fold_650_, v___x_652_);
v___x_654_ = lean_uint64_to_usize(v___x_653_);
v___x_655_ = lean_usize_of_nat(v___x_646_);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_sub(v___x_655_, v___x_656_);
v___x_658_ = lean_usize_land(v___x_654_, v___x_657_);
v___x_659_ = lean_array_uget_borrowed(v_buckets_645_, v___x_658_);
v___x_660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_644_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_661_, v_a_662_);
lean_dec_ref(v_a_662_);
lean_dec_ref(v_m_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v___x_665_, lean_object* v_goal_666_, lean_object* v_structId_667_, lean_object* v_as_668_, size_t v_sz_669_, size_t v_i_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_goal_666_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_b_671_);
return v___x_678_;
}
else
{
lean_object* v_snd_679_; lean_object* v_a_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_711_; 
v_snd_679_ = lean_ctor_get(v_b_671_, 1);
lean_inc(v_snd_679_);
lean_dec_ref(v_b_671_);
v_a_680_ = lean_array_uget(v_as_668_, v_i_670_);
v_fst_681_ = lean_ctor_get(v_a_680_, 0);
v_snd_682_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_711_ == 0)
{
v___x_684_ = v_a_680_;
v_isShared_685_ = v_isSharedCheck_711_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v_a_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_711_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_a_688_; uint8_t v___y_696_; uint8_t v___x_709_; 
v___x_686_ = lean_box(0);
v___x_709_ = lean_nat_dec_eq(v_structId_667_, v_snd_682_);
lean_dec(v_snd_682_);
if (v___x_709_ == 0)
{
v___y_696_ = v___x_709_;
goto v___jp_695_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_679_, v_fst_681_);
if (v___x_710_ == 0)
{
v___y_696_ = v___x_709_;
goto v___jp_695_;
}
else
{
lean_dec(v_fst_681_);
v_a_688_ = v_snd_679_;
goto v___jp_687_;
}
}
v___jp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_a_688_);
lean_ctor_set(v___x_684_, 0, v___x_686_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_688_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_670_, v___x_691_);
v_i_670_ = v___x_692_;
v_b_671_ = v___x_690_;
goto _start;
}
}
v___jp_695_:
{
if (v___y_696_ == 0)
{
lean_dec(v_fst_681_);
v_a_688_ = v_snd_679_;
goto v___jp_687_;
}
else
{
lean_object* v___x_697_; 
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v_fst_681_);
v___x_697_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_665_, v_snd_679_, v_fst_681_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
if (lean_obj_tag(v_a_698_) == 1)
{
lean_object* v_val_699_; lean_object* v___x_700_; 
v_val_699_ = lean_ctor_get(v_a_698_, 0);
lean_inc(v_val_699_);
lean_dec_ref(v_a_698_);
lean_inc_ref(v_goal_666_);
v___x_700_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_666_, v_fst_681_, v_val_699_, v_snd_679_);
v_a_688_ = v___x_700_;
goto v___jp_687_;
}
else
{
lean_dec(v_a_698_);
lean_dec(v_fst_681_);
v_a_688_ = v_snd_679_;
goto v___jp_687_;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_684_);
lean_dec(v_fst_681_);
lean_dec(v_snd_679_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_goal_666_);
v_a_701_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_697_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_697_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v___x_712_, lean_object* v_goal_713_, lean_object* v_structId_714_, lean_object* v_as_715_, lean_object* v_sz_716_, lean_object* v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
size_t v_sz_boxed_724_; size_t v_i_boxed_725_; lean_object* v_res_726_; 
v_sz_boxed_724_ = lean_unbox_usize(v_sz_716_);
lean_dec(v_sz_716_);
v_i_boxed_725_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_712_, v_goal_713_, v_structId_714_, v_as_715_, v_sz_boxed_724_, v_i_boxed_725_, v_b_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec_ref(v_as_715_);
lean_dec(v_structId_714_);
lean_dec_ref(v___x_712_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v___x_727_, lean_object* v_goal_728_, lean_object* v_structId_729_, lean_object* v_as_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_lt(v_i_732_, v_sz_731_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v_goal_728_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_b_733_);
return v___x_740_;
}
else
{
lean_object* v_snd_741_; lean_object* v_a_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_773_; 
v_snd_741_ = lean_ctor_get(v_b_733_, 1);
lean_inc(v_snd_741_);
lean_dec_ref(v_b_733_);
v_a_742_ = lean_array_uget(v_as_730_, v_i_732_);
v_fst_743_ = lean_ctor_get(v_a_742_, 0);
v_snd_744_ = lean_ctor_get(v_a_742_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_773_ == 0)
{
v___x_746_ = v_a_742_;
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v_a_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v_a_750_; uint8_t v___y_758_; uint8_t v___x_771_; 
v___x_748_ = lean_box(0);
v___x_771_ = lean_nat_dec_eq(v_structId_729_, v_snd_744_);
lean_dec(v_snd_744_);
if (v___x_771_ == 0)
{
v___y_758_ = v___x_771_;
goto v___jp_757_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_741_, v_fst_743_);
if (v___x_772_ == 0)
{
v___y_758_ = v___x_771_;
goto v___jp_757_;
}
else
{
lean_dec(v_fst_743_);
v_a_750_ = v_snd_741_;
goto v___jp_749_;
}
}
v___jp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_a_750_);
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_752_ = v___x_746_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_a_750_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_732_, v___x_753_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_727_, v_goal_728_, v_structId_729_, v_as_730_, v_sz_731_, v___x_754_, v___x_752_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_755_;
}
}
v___jp_757_:
{
if (v___y_758_ == 0)
{
lean_dec(v_fst_743_);
v_a_750_ = v_snd_741_;
goto v___jp_749_;
}
else
{
lean_object* v___x_759_; 
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v_fst_743_);
v___x_759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_727_, v_snd_741_, v_fst_743_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
if (lean_obj_tag(v_a_760_) == 1)
{
lean_object* v_val_761_; lean_object* v___x_762_; 
v_val_761_ = lean_ctor_get(v_a_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref(v_a_760_);
lean_inc_ref(v_goal_728_);
v___x_762_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_728_, v_fst_743_, v_val_761_, v_snd_741_);
v_a_750_ = v___x_762_;
goto v___jp_749_;
}
else
{
lean_dec(v_a_760_);
lean_dec(v_fst_743_);
v_a_750_ = v_snd_741_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_746_);
lean_dec(v_fst_743_);
lean_dec(v_snd_741_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v_goal_728_);
v_a_763_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_759_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_759_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v___x_774_, lean_object* v_goal_775_, lean_object* v_structId_776_, lean_object* v_as_777_, lean_object* v_sz_778_, lean_object* v_i_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
size_t v_sz_boxed_786_; size_t v_i_boxed_787_; lean_object* v_res_788_; 
v_sz_boxed_786_ = lean_unbox_usize(v_sz_778_);
lean_dec(v_sz_778_);
v_i_boxed_787_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_774_, v_goal_775_, v_structId_776_, v_as_777_, v_sz_boxed_786_, v_i_boxed_787_, v_b_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v_as_777_);
lean_dec(v_structId_776_);
lean_dec_ref(v___x_774_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v___x_789_, lean_object* v_goal_790_, lean_object* v_structId_791_, lean_object* v_inh_792_, lean_object* v_n_793_, lean_object* v_b_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
if (lean_obj_tag(v_n_793_) == 0)
{
lean_object* v_cs_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_834_; 
v_cs_800_ = lean_ctor_get(v_n_793_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_n_793_);
if (v_isSharedCheck_834_ == 0)
{
v___x_802_ = v_n_793_;
v_isShared_803_ = v_isSharedCheck_834_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_cs_800_);
lean_dec(v_n_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_834_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_b_794_);
v_sz_806_ = lean_array_size(v_cs_800_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v___x_789_, v_goal_790_, v_structId_791_, v_inh_792_, v_cs_800_, v_sz_806_, v___x_807_, v___x_805_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec_ref(v_cs_800_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_825_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_825_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_825_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_825_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; 
v_fst_813_ = lean_ctor_get(v_a_809_, 0);
if (lean_obj_tag(v_fst_813_) == 0)
{
lean_object* v_snd_814_; lean_object* v___x_816_; 
v_snd_814_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_814_);
lean_dec(v_a_809_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 1);
lean_ctor_set(v___x_802_, 0, v_snd_814_);
v___x_816_ = v___x_802_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_snd_814_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_816_);
v___x_818_ = v___x_811_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; 
lean_inc_ref(v_fst_813_);
lean_dec(v_a_809_);
lean_del_object(v___x_802_);
v_val_821_ = lean_ctor_get(v_fst_813_, 0);
lean_inc(v_val_821_);
lean_dec_ref(v_fst_813_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_val_821_);
v___x_823_ = v___x_811_;
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
lean_del_object(v___x_802_);
v_a_826_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_808_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_808_);
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
}
else
{
lean_object* v_vs_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_869_; 
v_vs_835_ = lean_ctor_get(v_n_793_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_n_793_);
if (v_isSharedCheck_869_ == 0)
{
v___x_837_ = v_n_793_;
v_isShared_838_ = v_isSharedCheck_869_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_vs_835_);
lean_dec(v_n_793_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_869_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_b_794_);
v_sz_841_ = lean_array_size(v_vs_835_);
v___x_842_ = ((size_t)0ULL);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_789_, v_goal_790_, v_structId_791_, v_vs_835_, v_sz_841_, v___x_842_, v___x_840_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec_ref(v_vs_835_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_860_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_860_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_860_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_860_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; 
v_fst_848_ = lean_ctor_get(v_a_844_, 0);
if (lean_obj_tag(v_fst_848_) == 0)
{
lean_object* v_snd_849_; lean_object* v___x_851_; 
v_snd_849_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_snd_849_);
lean_dec(v_a_844_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_snd_849_);
v___x_851_ = v___x_837_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_snd_849_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_851_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; 
lean_inc_ref(v_fst_848_);
lean_dec(v_a_844_);
lean_del_object(v___x_837_);
v_val_856_ = lean_ctor_get(v_fst_848_, 0);
lean_inc(v_val_856_);
lean_dec_ref(v_fst_848_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v_val_856_);
v___x_858_ = v___x_846_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_val_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_837_);
v_a_861_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_843_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_843_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v___x_870_, lean_object* v_goal_871_, lean_object* v_structId_872_, lean_object* v_inh_873_, lean_object* v_as_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_lt(v_i_876_, v_sz_875_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v_goal_871_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_b_877_);
return v___x_884_;
}
else
{
lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_919_; 
v_snd_885_ = lean_ctor_get(v_b_877_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_b_877_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_b_877_, 0);
lean_dec(v_unused_920_);
v___x_887_ = v_b_877_;
v_isShared_888_ = v_isSharedCheck_919_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_dec(v_b_877_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_919_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_array_uget_borrowed(v_as_874_, v_i_876_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v_snd_885_);
lean_inc(v_a_889_);
lean_inc_ref(v_goal_871_);
v___x_890_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v___x_870_, v_goal_871_, v_structId_872_, v_inh_873_, v_a_889_, v_snd_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_910_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_910_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_897_; 
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v_goal_871_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_a_891_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_895_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_885_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_897_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_del_object(v___x_893_);
lean_dec(v_snd_885_);
v_a_902_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v_a_891_);
v___x_903_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_a_902_);
lean_ctor_set(v___x_887_, 0, v___x_903_);
v___x_905_ = v___x_887_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_902_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
size_t v___x_906_; size_t v___x_907_; 
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_876_, v___x_906_);
v_i_876_ = v___x_907_;
v_b_877_ = v___x_905_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_del_object(v___x_887_);
lean_dec(v_snd_885_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v_goal_871_);
v_a_911_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_890_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_890_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v___x_921_, lean_object* v_goal_922_, lean_object* v_structId_923_, lean_object* v_inh_924_, lean_object* v_as_925_, lean_object* v_sz_926_, lean_object* v_i_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_935_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v___x_921_, v_goal_922_, v_structId_923_, v_inh_924_, v_as_925_, v_sz_boxed_934_, v_i_boxed_935_, v_b_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec_ref(v_as_925_);
lean_dec_ref(v_inh_924_);
lean_dec(v_structId_923_);
lean_dec_ref(v___x_921_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v___x_937_, lean_object* v_goal_938_, lean_object* v_structId_939_, lean_object* v_inh_940_, lean_object* v_n_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v___x_937_, v_goal_938_, v_structId_939_, v_inh_940_, v_n_941_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec_ref(v_inh_940_);
lean_dec(v_structId_939_);
lean_dec_ref(v___x_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v___x_949_, lean_object* v_goal_950_, lean_object* v_structId_951_, lean_object* v_as_952_, size_t v_sz_953_, size_t v_i_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_lt(v_i_954_, v_sz_953_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_goal_950_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_b_955_);
return v___x_962_;
}
else
{
lean_object* v_snd_963_; lean_object* v_a_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_995_; 
v_snd_963_ = lean_ctor_get(v_b_955_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v_b_955_);
v_a_964_ = lean_array_uget(v_as_952_, v_i_954_);
v_fst_965_ = lean_ctor_get(v_a_964_, 0);
v_snd_966_ = lean_ctor_get(v_a_964_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_995_ == 0)
{
v___x_968_ = v_a_964_;
v_isShared_969_ = v_isSharedCheck_995_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v_a_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_995_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v_a_972_; uint8_t v___y_980_; uint8_t v___x_993_; 
v___x_970_ = lean_box(0);
v___x_993_ = lean_nat_dec_eq(v_structId_951_, v_snd_966_);
lean_dec(v_snd_966_);
if (v___x_993_ == 0)
{
v___y_980_ = v___x_993_;
goto v___jp_979_;
}
else
{
uint8_t v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_963_, v_fst_965_);
if (v___x_994_ == 0)
{
v___y_980_ = v___x_993_;
goto v___jp_979_;
}
else
{
lean_dec(v_fst_965_);
v_a_972_ = v_snd_963_;
goto v___jp_971_;
}
}
v___jp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_a_972_);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_974_ = v___x_968_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
size_t v___x_975_; size_t v___x_976_; 
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_954_, v___x_975_);
v_i_954_ = v___x_976_;
v_b_955_ = v___x_974_;
goto _start;
}
}
v___jp_979_:
{
if (v___y_980_ == 0)
{
lean_dec(v_fst_965_);
v_a_972_ = v_snd_963_;
goto v___jp_971_;
}
else
{
lean_object* v___x_981_; 
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v_fst_965_);
v___x_981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_949_, v_snd_963_, v_fst_965_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v_a_982_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; 
v_val_983_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v_a_982_);
lean_inc_ref(v_goal_950_);
v___x_984_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_950_, v_fst_965_, v_val_983_, v_snd_963_);
v_a_972_ = v___x_984_;
goto v___jp_971_;
}
else
{
lean_dec(v_a_982_);
lean_dec(v_fst_965_);
v_a_972_ = v_snd_963_;
goto v___jp_971_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_del_object(v___x_968_);
lean_dec(v_fst_965_);
lean_dec(v_snd_963_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_goal_950_);
v_a_985_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_981_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v___x_996_, lean_object* v_goal_997_, lean_object* v_structId_998_, lean_object* v_as_999_, lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_b_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
size_t v_sz_boxed_1008_; size_t v_i_boxed_1009_; lean_object* v_res_1010_; 
v_sz_boxed_1008_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1009_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_996_, v_goal_997_, v_structId_998_, v_as_999_, v_sz_boxed_1008_, v_i_boxed_1009_, v_b_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec_ref(v_as_999_);
lean_dec(v_structId_998_);
lean_dec_ref(v___x_996_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v___x_1011_, lean_object* v_goal_1012_, lean_object* v_structId_1013_, lean_object* v_as_1014_, size_t v_sz_1015_, size_t v_i_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_usize_dec_lt(v_i_1016_, v_sz_1015_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_goal_1012_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_b_1017_);
return v___x_1024_;
}
else
{
lean_object* v_snd_1025_; lean_object* v_a_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1057_; 
v_snd_1025_ = lean_ctor_get(v_b_1017_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v_b_1017_);
v_a_1026_ = lean_array_uget(v_as_1014_, v_i_1016_);
v_fst_1027_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1030_ = v_a_1026_;
v_isShared_1031_ = v_isSharedCheck_1057_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1057_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v_a_1034_; uint8_t v___y_1042_; uint8_t v___x_1055_; 
v___x_1032_ = lean_box(0);
v___x_1055_ = lean_nat_dec_eq(v_structId_1013_, v_snd_1028_);
lean_dec(v_snd_1028_);
if (v___x_1055_ == 0)
{
v___y_1042_ = v___x_1055_;
goto v___jp_1041_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_1025_, v_fst_1027_);
if (v___x_1056_ == 0)
{
v___y_1042_ = v___x_1055_;
goto v___jp_1041_;
}
else
{
lean_dec(v_fst_1027_);
v_a_1034_ = v_snd_1025_;
goto v___jp_1033_;
}
}
v___jp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v_a_1034_);
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1036_ = v___x_1030_;
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
v___x_1038_ = lean_usize_add(v_i_1016_, v___x_1037_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_1011_, v_goal_1012_, v_structId_1013_, v_as_1014_, v_sz_1015_, v___x_1038_, v___x_1036_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1039_;
}
}
v___jp_1041_:
{
if (v___y_1042_ == 0)
{
lean_dec(v_fst_1027_);
v_a_1034_ = v_snd_1025_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1043_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v_fst_1027_);
v___x_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_1011_, v_snd_1025_, v_fst_1027_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
if (lean_obj_tag(v_a_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v_a_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v_a_1044_);
lean_inc_ref(v_goal_1012_);
v___x_1046_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1012_, v_fst_1027_, v_val_1045_, v_snd_1025_);
v_a_1034_ = v___x_1046_;
goto v___jp_1033_;
}
else
{
lean_dec(v_a_1044_);
lean_dec(v_fst_1027_);
v_a_1034_ = v_snd_1025_;
goto v___jp_1033_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1030_);
lean_dec(v_fst_1027_);
lean_dec(v_snd_1025_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_goal_1012_);
v_a_1047_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1043_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1043_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v___x_1058_, lean_object* v_goal_1059_, lean_object* v_structId_1060_, lean_object* v_as_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
size_t v_sz_boxed_1070_; size_t v_i_boxed_1071_; lean_object* v_res_1072_; 
v_sz_boxed_1070_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1058_, v_goal_1059_, v_structId_1060_, v_as_1061_, v_sz_boxed_1070_, v_i_boxed_1071_, v_b_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v_as_1061_);
lean_dec(v_structId_1060_);
lean_dec_ref(v___x_1058_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1073_, lean_object* v_goal_1074_, lean_object* v_structId_1075_, lean_object* v_t_1076_, lean_object* v_init_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_root_1083_; lean_object* v_tail_1084_; lean_object* v___x_1085_; 
v_root_1083_ = lean_ctor_get(v_t_1076_, 0);
lean_inc_ref(v_root_1083_);
v_tail_1084_ = lean_ctor_get(v_t_1076_, 1);
lean_inc_ref(v_tail_1084_);
lean_dec_ref(v_t_1076_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc_ref(v_init_1077_);
lean_inc_ref(v_goal_1074_);
v___x_1085_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v___x_1073_, v_goal_1074_, v_structId_1075_, v_init_1077_, v_root_1083_, v_init_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec_ref(v_init_1077_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1122_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1122_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1122_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
if (lean_obj_tag(v_a_1086_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; 
lean_dec_ref(v_tail_1084_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_goal_1074_);
v_a_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_a_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; size_t v_sz_1097_; size_t v___x_1098_; lean_object* v___x_1099_; 
lean_del_object(v___x_1088_);
v_a_1094_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v_a_1086_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1094_);
v_sz_1097_ = lean_array_size(v_tail_1084_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1073_, v_goal_1074_, v_structId_1075_, v_tail_1084_, v_sz_1097_, v___x_1098_, v___x_1096_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec_ref(v_tail_1084_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1113_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1113_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1113_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_fst_1104_; 
v_fst_1104_ = lean_ctor_get(v_a_1100_, 0);
if (lean_obj_tag(v_fst_1104_) == 0)
{
lean_object* v_snd_1105_; lean_object* v___x_1107_; 
v_snd_1105_ = lean_ctor_get(v_a_1100_, 1);
lean_inc(v_snd_1105_);
lean_dec(v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_snd_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_snd_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
else
{
lean_object* v_val_1109_; lean_object* v___x_1111_; 
lean_inc_ref(v_fst_1104_);
lean_dec(v_a_1100_);
v_val_1109_ = lean_ctor_get(v_fst_1104_, 0);
lean_inc(v_val_1109_);
lean_dec_ref(v_fst_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_val_1109_);
v___x_1111_ = v___x_1102_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_val_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1099_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1099_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_tail_1084_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_goal_1074_);
v_a_1123_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1085_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1085_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1131_, lean_object* v_goal_1132_, lean_object* v_structId_1133_, lean_object* v_t_1134_, lean_object* v_init_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1131_, v_goal_1132_, v_structId_1133_, v_t_1134_, v_init_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v_structId_1133_);
lean_dec_ref(v___x_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1142_, lean_object* v_structId_1143_, lean_object* v_model_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1151_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1150_, v_goal_1142_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v_structs_1153_; lean_object* v_exprToStructIdEntries_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1151_);
v_structs_1153_ = lean_ctor_get(v_a_1152_, 0);
lean_inc_ref(v_structs_1153_);
v_exprToStructIdEntries_1154_ = lean_ctor_get(v_a_1152_, 3);
lean_inc_ref(v_exprToStructIdEntries_1154_);
lean_dec(v_a_1152_);
v___x_1155_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1156_ = lean_array_get(v___x_1155_, v_structs_1153_, v_structId_1143_);
lean_dec_ref(v_structs_1153_);
v___x_1157_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1156_, v_goal_1142_, v_structId_1143_, v_exprToStructIdEntries_1154_, v_model_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_a_1148_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_model_1144_);
lean_dec_ref(v_goal_1142_);
v_a_1158_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v___x_1151_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1151_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_ref_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v_ref_1162_ = lean_ctor_get(v_a_1147_, 5);
lean_inc(v_ref_1162_);
lean_dec_ref(v_a_1147_);
v___x_1163_ = lean_io_error_to_string(v_a_1158_);
v___x_1164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
v___x_1165_ = l_Lean_MessageData_ofFormat(v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_ref_1162_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1166_);
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1171_, lean_object* v_structId_1172_, lean_object* v_model_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1171_, v_structId_1172_, v_model_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_structId_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1180_, lean_object* v_m_1181_, lean_object* v_a_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1181_, v_a_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1184_, v_m_1185_, v_a_1186_);
lean_dec_ref(v_a_1186_);
lean_dec_ref(v_m_1185_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1189_, lean_object* v_a_1190_, lean_object* v_x_1191_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1190_, v_x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1193_, lean_object* v_a_1194_, lean_object* v_x_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1193_, v_a_1194_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec_ref(v_a_1194_);
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
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_goal_1198_);
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
lean_inc_ref(v_goal_1198_);
v___x_1216_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1198_, v_a_1215_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_a_1220_; uint8_t v___x_1227_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
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
lean_inc(v___y_1207_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc(v_a_1217_);
lean_inc_ref(v_type_1228_);
v___x_1229_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1228_, v_a_1217_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; uint8_t v___x_1231_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1229_);
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
lean_inc_ref(v___x_1199_);
v___x_1233_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1199_, v_self_1232_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1235_; 
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref(v___x_1233_);
lean_inc_ref(v_goal_1198_);
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
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_goal_1198_);
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
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_goal_1198_);
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
lean_dec_ref(v_as_1256_);
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
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_goal_1268_);
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
lean_inc_ref(v_goal_1268_);
v___x_1286_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1268_, v_a_1285_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v_a_1290_; uint8_t v___x_1297_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
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
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v_a_1287_);
lean_inc_ref(v_type_1298_);
v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1298_, v_a_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; uint8_t v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
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
lean_inc_ref(v___x_1269_);
v___x_1303_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1269_, v_self_1302_);
if (lean_obj_tag(v___x_1303_) == 1)
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref(v___x_1303_);
lean_inc_ref(v_goal_1268_);
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
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_goal_1268_);
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
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_goal_1268_);
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
lean_dec_ref(v_as_1326_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_goal_1338_, lean_object* v___x_1339_, lean_object* v_inh_1340_, lean_object* v_n_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
if (lean_obj_tag(v_n_1341_) == 0)
{
lean_object* v_cs_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1382_; 
v_cs_1348_ = lean_ctor_get(v_n_1341_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_n_1341_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1350_ = v_n_1341_;
v_isShared_1351_ = v_isSharedCheck_1382_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_cs_1348_);
lean_dec(v_n_1341_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1382_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_b_1342_);
v_sz_1354_ = lean_array_size(v_cs_1348_);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_goal_1338_, v___x_1339_, v_inh_1340_, v_cs_1348_, v_sz_1354_, v___x_1355_, v___x_1353_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec_ref(v_cs_1348_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1373_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_fst_1361_; 
v_fst_1361_ = lean_ctor_get(v_a_1357_, 0);
if (lean_obj_tag(v_fst_1361_) == 0)
{
lean_object* v_snd_1362_; lean_object* v___x_1364_; 
v_snd_1362_ = lean_ctor_get(v_a_1357_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_a_1357_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 1);
lean_ctor_set(v___x_1350_, 0, v_snd_1362_);
v___x_1364_ = v___x_1350_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_snd_1362_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1364_);
v___x_1366_ = v___x_1359_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; 
lean_inc_ref(v_fst_1361_);
lean_dec(v_a_1357_);
lean_del_object(v___x_1350_);
v_val_1369_ = lean_ctor_get(v_fst_1361_, 0);
lean_inc(v_val_1369_);
lean_dec_ref(v_fst_1361_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_val_1369_);
v___x_1371_ = v___x_1359_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_val_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1350_);
v_a_1374_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1356_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1356_);
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
else
{
lean_object* v_vs_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1417_; 
v_vs_1383_ = lean_ctor_get(v_n_1341_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_n_1341_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1385_ = v_n_1341_;
v_isShared_1386_ = v_isSharedCheck_1417_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_vs_1383_);
lean_dec(v_n_1341_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1417_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v_b_1342_);
v_sz_1389_ = lean_array_size(v_vs_1383_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1338_, v___x_1339_, v_vs_1383_, v_sz_1389_, v___x_1390_, v___x_1388_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec_ref(v_vs_1383_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1408_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1408_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1408_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v_fst_1396_; 
v_fst_1396_ = lean_ctor_get(v_a_1392_, 0);
if (lean_obj_tag(v_fst_1396_) == 0)
{
lean_object* v_snd_1397_; lean_object* v___x_1399_; 
v_snd_1397_ = lean_ctor_get(v_a_1392_, 1);
lean_inc(v_snd_1397_);
lean_dec(v_a_1392_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_snd_1397_);
v___x_1399_ = v___x_1385_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_snd_1397_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1399_);
v___x_1401_ = v___x_1394_;
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
lean_object* v_val_1404_; lean_object* v___x_1406_; 
lean_inc_ref(v_fst_1396_);
lean_dec(v_a_1392_);
lean_del_object(v___x_1385_);
v_val_1404_ = lean_ctor_get(v_fst_1396_, 0);
lean_inc(v_val_1404_);
lean_dec_ref(v_fst_1396_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v_val_1404_);
v___x_1406_ = v___x_1394_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_val_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1385_);
v_a_1409_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1391_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1391_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_goal_1418_, lean_object* v___x_1419_, lean_object* v_inh_1420_, lean_object* v_as_1421_, size_t v_sz_1422_, size_t v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_lt(v_i_1423_, v_sz_1422_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_goal_1418_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_b_1424_);
return v___x_1431_;
}
else
{
lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1466_; 
v_snd_1432_ = lean_ctor_get(v_b_1424_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_b_1424_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_b_1424_, 0);
lean_dec(v_unused_1467_);
v___x_1434_ = v_b_1424_;
v_isShared_1435_ = v_isSharedCheck_1466_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_dec(v_b_1424_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1466_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_array_uget_borrowed(v_as_1421_, v_i_1423_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v_snd_1432_);
lean_inc(v_a_1436_);
lean_inc_ref(v___x_1419_);
lean_inc_ref(v_goal_1418_);
v___x_1437_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_goal_1418_, v___x_1419_, v_inh_1420_, v_a_1436_, v_snd_1432_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1457_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
if (lean_obj_tag(v_a_1438_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_goal_1418_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1438_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1442_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1432_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1444_);
v___x_1446_ = v___x_1440_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_del_object(v___x_1440_);
lean_dec(v_snd_1432_);
v_a_1449_ = lean_ctor_get(v_a_1438_, 0);
lean_inc(v_a_1449_);
lean_dec_ref(v_a_1438_);
v___x_1450_ = lean_box(0);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_a_1449_);
lean_ctor_set(v___x_1434_, 0, v___x_1450_);
v___x_1452_ = v___x_1434_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_a_1449_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
size_t v___x_1453_; size_t v___x_1454_; 
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1423_, v___x_1453_);
v_i_1423_ = v___x_1454_;
v_b_1424_ = v___x_1452_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_goal_1418_);
v_a_1458_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1437_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1437_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_goal_1468_, lean_object* v___x_1469_, lean_object* v_inh_1470_, lean_object* v_as_1471_, lean_object* v_sz_1472_, lean_object* v_i_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1472_);
lean_dec(v_sz_1472_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_goal_1468_, v___x_1469_, v_inh_1470_, v_as_1471_, v_sz_boxed_1480_, v_i_boxed_1481_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec_ref(v_as_1471_);
lean_dec_ref(v_inh_1470_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_goal_1483_, lean_object* v___x_1484_, lean_object* v_inh_1485_, lean_object* v_n_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_goal_1483_, v___x_1484_, v_inh_1485_, v_n_1486_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec_ref(v_inh_1485_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1494_, lean_object* v___x_1495_, lean_object* v_as_1496_, size_t v_sz_1497_, size_t v_i_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1498_, v_sz_1497_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_goal_1494_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_b_1499_);
return v___x_1506_;
}
else
{
lean_object* v_snd_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1548_; 
v_snd_1507_ = lean_ctor_get(v_b_1499_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_b_1499_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_b_1499_, 0);
lean_dec(v_unused_1549_);
v___x_1509_ = v_b_1499_;
v_isShared_1510_ = v_isSharedCheck_1548_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1507_);
lean_dec(v_b_1499_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1548_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_array_uget_borrowed(v_as_1496_, v_i_1498_);
lean_inc(v_a_1511_);
lean_inc_ref(v_goal_1494_);
v___x_1512_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1494_, v_a_1511_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v_a_1516_; uint8_t v___x_1523_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = lean_box(0);
v___x_1523_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1513_);
if (v___x_1523_ == 0)
{
lean_dec(v_a_1513_);
v_a_1516_ = v_snd_1507_;
goto v___jp_1515_;
}
else
{
lean_object* v_type_1524_; lean_object* v___x_1525_; 
v_type_1524_ = lean_ctor_get(v___x_1495_, 2);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v_a_1513_);
lean_inc_ref(v_type_1524_);
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1524_, v_a_1513_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; uint8_t v___x_1527_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = lean_unbox(v_a_1526_);
lean_dec(v_a_1526_);
if (v___x_1527_ == 0)
{
lean_dec(v_a_1513_);
v_a_1516_ = v_snd_1507_;
goto v___jp_1515_;
}
else
{
lean_object* v_self_1528_; lean_object* v___x_1529_; 
v_self_1528_ = lean_ctor_get(v_a_1513_, 0);
lean_inc_ref(v_self_1528_);
lean_dec(v_a_1513_);
lean_inc_ref(v___x_1495_);
v___x_1529_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1495_, v_self_1528_);
if (lean_obj_tag(v___x_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1531_; 
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1530_);
lean_dec_ref(v___x_1529_);
lean_inc_ref(v_goal_1494_);
v___x_1531_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1494_, v_self_1528_, v_val_1530_, v_snd_1507_);
v_a_1516_ = v___x_1531_;
goto v___jp_1515_;
}
else
{
lean_dec(v___x_1529_);
lean_dec_ref(v_self_1528_);
v_a_1516_ = v_snd_1507_;
goto v___jp_1515_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_a_1513_);
lean_del_object(v___x_1509_);
lean_dec(v_snd_1507_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_goal_1494_);
v_a_1532_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1525_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1525_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
v___jp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_a_1516_);
lean_ctor_set(v___x_1509_, 0, v___x_1514_);
v___x_1518_ = v___x_1509_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1498_, v___x_1519_);
v_i_1498_ = v___x_1520_;
v_b_1499_ = v___x_1518_;
goto _start;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_del_object(v___x_1509_);
lean_dec(v_snd_1507_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_goal_1494_);
v_a_1540_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1512_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1512_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1550_, lean_object* v___x_1551_, lean_object* v_as_1552_, lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
size_t v_sz_boxed_1561_; size_t v_i_boxed_1562_; lean_object* v_res_1563_; 
v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1562_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1550_, v___x_1551_, v_as_1552_, v_sz_boxed_1561_, v_i_boxed_1562_, v_b_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec_ref(v_as_1552_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1564_, lean_object* v___x_1565_, lean_object* v_as_1566_, size_t v_sz_1567_, size_t v_i_1568_, lean_object* v_b_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_usize_dec_lt(v_i_1568_, v_sz_1567_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_goal_1564_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_b_1569_);
return v___x_1576_;
}
else
{
lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1618_; 
v_snd_1577_ = lean_ctor_get(v_b_1569_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_b_1569_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_b_1569_, 0);
lean_dec(v_unused_1619_);
v___x_1579_ = v_b_1569_;
v_isShared_1580_ = v_isSharedCheck_1618_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_dec(v_b_1569_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1618_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_array_uget_borrowed(v_as_1566_, v_i_1568_);
lean_inc(v_a_1581_);
lean_inc_ref(v_goal_1564_);
v___x_1582_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1564_, v_a_1581_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v_a_1586_; uint8_t v___x_1593_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = lean_box(0);
v___x_1593_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1583_);
if (v___x_1593_ == 0)
{
lean_dec(v_a_1583_);
v_a_1586_ = v_snd_1577_;
goto v___jp_1585_;
}
else
{
lean_object* v_type_1594_; lean_object* v___x_1595_; 
v_type_1594_ = lean_ctor_get(v___x_1565_, 2);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v_a_1583_);
lean_inc_ref(v_type_1594_);
v___x_1595_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1594_, v_a_1583_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = lean_unbox(v_a_1596_);
lean_dec(v_a_1596_);
if (v___x_1597_ == 0)
{
lean_dec(v_a_1583_);
v_a_1586_ = v_snd_1577_;
goto v___jp_1585_;
}
else
{
lean_object* v_self_1598_; lean_object* v___x_1599_; 
v_self_1598_ = lean_ctor_get(v_a_1583_, 0);
lean_inc_ref(v_self_1598_);
lean_dec(v_a_1583_);
lean_inc_ref(v___x_1565_);
v___x_1599_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1565_, v_self_1598_);
if (lean_obj_tag(v___x_1599_) == 1)
{
lean_object* v_val_1600_; lean_object* v___x_1601_; 
v_val_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_val_1600_);
lean_dec_ref(v___x_1599_);
lean_inc_ref(v_goal_1564_);
v___x_1601_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1564_, v_self_1598_, v_val_1600_, v_snd_1577_);
v_a_1586_ = v___x_1601_;
goto v___jp_1585_;
}
else
{
lean_dec(v___x_1599_);
lean_dec_ref(v_self_1598_);
v_a_1586_ = v_snd_1577_;
goto v___jp_1585_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1583_);
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_goal_1564_);
v_a_1602_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1595_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1595_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
v___jp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_a_1586_);
lean_ctor_set(v___x_1579_, 0, v___x_1584_);
v___x_1588_ = v___x_1579_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1586_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1568_, v___x_1589_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1564_, v___x_1565_, v_as_1566_, v_sz_1567_, v___x_1590_, v___x_1588_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v___x_1565_);
lean_dec_ref(v_goal_1564_);
v_a_1610_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1582_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1582_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1620_, lean_object* v___x_1621_, lean_object* v_as_1622_, lean_object* v_sz_1623_, lean_object* v_i_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
size_t v_sz_boxed_1631_; size_t v_i_boxed_1632_; lean_object* v_res_1633_; 
v_sz_boxed_1631_ = lean_unbox_usize(v_sz_1623_);
lean_dec(v_sz_1623_);
v_i_boxed_1632_ = lean_unbox_usize(v_i_1624_);
lean_dec(v_i_1624_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1620_, v___x_1621_, v_as_1622_, v_sz_boxed_1631_, v_i_boxed_1632_, v_b_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v_as_1622_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1634_, lean_object* v___x_1635_, lean_object* v_t_1636_, lean_object* v_init_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_root_1643_; lean_object* v_tail_1644_; lean_object* v___x_1645_; 
v_root_1643_ = lean_ctor_get(v_t_1636_, 0);
lean_inc_ref(v_root_1643_);
v_tail_1644_ = lean_ctor_get(v_t_1636_, 1);
lean_inc_ref(v_tail_1644_);
lean_dec_ref(v_t_1636_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc_ref(v_init_1637_);
lean_inc_ref(v___x_1635_);
lean_inc_ref(v_goal_1634_);
v___x_1645_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_goal_1634_, v___x_1635_, v_init_1637_, v_root_1643_, v_init_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v_init_1637_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1682_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1682_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1682_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
if (lean_obj_tag(v_a_1646_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; 
lean_dec_ref(v_tail_1644_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v_goal_1634_);
v_a_1650_ = lean_ctor_get(v_a_1646_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v_a_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v_a_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; size_t v_sz_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
lean_del_object(v___x_1648_);
v_a_1654_ = lean_ctor_get(v_a_1646_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v_a_1646_);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_a_1654_);
v_sz_1657_ = lean_array_size(v_tail_1644_);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1634_, v___x_1635_, v_tail_1644_, v_sz_1657_, v___x_1658_, v___x_1656_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v_tail_1644_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1673_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_fst_1664_; 
v_fst_1664_ = lean_ctor_get(v_a_1660_, 0);
if (lean_obj_tag(v_fst_1664_) == 0)
{
lean_object* v_snd_1665_; lean_object* v___x_1667_; 
v_snd_1665_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1665_);
lean_dec(v_a_1660_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v_snd_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_snd_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
else
{
lean_object* v_val_1669_; lean_object* v___x_1671_; 
lean_inc_ref(v_fst_1664_);
lean_dec(v_a_1660_);
v_val_1669_ = lean_ctor_get(v_fst_1664_, 0);
lean_inc(v_val_1669_);
lean_dec_ref(v_fst_1664_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v_val_1669_);
v___x_1671_ = v___x_1662_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_val_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1659_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1659_);
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
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_tail_1644_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v_goal_1634_);
v_a_1683_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1645_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1645_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1691_, lean_object* v___x_1692_, lean_object* v_t_1693_, lean_object* v_init_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1691_, v___x_1692_, v_t_1693_, v_init_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1701_, lean_object* v_as_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref(v_goal_1701_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_b_1705_);
return v___x_1712_;
}
else
{
lean_object* v_snd_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1744_; 
v_snd_1713_ = lean_ctor_get(v_b_1705_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_b_1705_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_b_1705_, 0);
lean_dec(v_unused_1745_);
v___x_1715_ = v_b_1705_;
v_isShared_1716_ = v_isSharedCheck_1744_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_snd_1713_);
lean_dec(v_b_1705_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1744_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_array_uget_borrowed(v_as_1702_, v_i_1704_);
lean_inc(v_a_1717_);
lean_inc_ref(v_goal_1701_);
v___x_1718_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1701_, v_a_1717_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v_self_1720_; lean_object* v___x_1721_; lean_object* v_a_1723_; lean_object* v___x_1730_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v_self_1720_ = lean_ctor_get(v_a_1719_, 0);
lean_inc_ref(v_self_1720_);
lean_dec(v_a_1719_);
v___x_1721_ = lean_box(0);
lean_inc_ref(v_self_1720_);
v___x_1730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1720_);
if (lean_obj_tag(v___x_1730_) == 1)
{
lean_object* v_val_1731_; lean_object* v___x_1732_; 
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1713_, v_val_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1713_, v_self_1720_);
lean_dec_ref(v_self_1720_);
if (lean_obj_tag(v___x_1733_) == 1)
{
lean_object* v_val_1734_; lean_object* v___x_1735_; 
v_val_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_val_1734_);
lean_dec_ref(v___x_1733_);
lean_inc_ref(v_goal_1701_);
v___x_1735_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1701_, v_val_1731_, v_val_1734_, v_snd_1713_);
v_a_1723_ = v___x_1735_;
goto v___jp_1722_;
}
else
{
lean_dec(v___x_1733_);
lean_dec(v_val_1731_);
v_a_1723_ = v_snd_1713_;
goto v___jp_1722_;
}
}
else
{
lean_dec_ref(v___x_1732_);
lean_dec(v_val_1731_);
lean_dec_ref(v_self_1720_);
v_a_1723_ = v_snd_1713_;
goto v___jp_1722_;
}
}
else
{
lean_dec(v___x_1730_);
lean_dec_ref(v_self_1720_);
v_a_1723_ = v_snd_1713_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_a_1723_);
lean_ctor_set(v___x_1715_, 0, v___x_1721_);
v___x_1725_ = v___x_1715_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_a_1723_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
size_t v___x_1726_; size_t v___x_1727_; 
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1704_, v___x_1726_);
v_i_1704_ = v___x_1727_;
v_b_1705_ = v___x_1725_;
goto _start;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1715_);
lean_dec(v_snd_1713_);
lean_dec_ref(v_goal_1701_);
v_a_1736_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1718_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1718_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1746_, lean_object* v_as_1747_, lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1746_, v_as_1747_, v_sz_boxed_1756_, v_i_boxed_1757_, v_b_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec_ref(v_as_1747_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1759_, lean_object* v_as_1760_, size_t v_sz_1761_, size_t v_i_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_lt(v_i_1762_, v_sz_1761_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v_goal_1759_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1763_);
return v___x_1770_;
}
else
{
lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1802_; 
v_snd_1771_ = lean_ctor_get(v_b_1763_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_b_1763_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_b_1763_, 0);
lean_dec(v_unused_1803_);
v___x_1773_ = v_b_1763_;
v_isShared_1774_ = v_isSharedCheck_1802_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_dec(v_b_1763_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1802_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_array_uget_borrowed(v_as_1760_, v_i_1762_);
lean_inc(v_a_1775_);
lean_inc_ref(v_goal_1759_);
v___x_1776_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1759_, v_a_1775_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v_self_1778_; lean_object* v___x_1779_; lean_object* v_a_1781_; lean_object* v___x_1788_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v_self_1778_ = lean_ctor_get(v_a_1777_, 0);
lean_inc_ref(v_self_1778_);
lean_dec(v_a_1777_);
v___x_1779_ = lean_box(0);
lean_inc_ref(v_self_1778_);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1778_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1790_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1771_, v_val_1789_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1771_, v_self_1778_);
lean_dec_ref(v_self_1778_);
if (lean_obj_tag(v___x_1791_) == 1)
{
lean_object* v_val_1792_; lean_object* v___x_1793_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref(v___x_1791_);
lean_inc_ref(v_goal_1759_);
v___x_1793_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1759_, v_val_1789_, v_val_1792_, v_snd_1771_);
v_a_1781_ = v___x_1793_;
goto v___jp_1780_;
}
else
{
lean_dec(v___x_1791_);
lean_dec(v_val_1789_);
v_a_1781_ = v_snd_1771_;
goto v___jp_1780_;
}
}
else
{
lean_dec_ref(v___x_1790_);
lean_dec(v_val_1789_);
lean_dec_ref(v_self_1778_);
v_a_1781_ = v_snd_1771_;
goto v___jp_1780_;
}
}
else
{
lean_dec(v___x_1788_);
lean_dec_ref(v_self_1778_);
v_a_1781_ = v_snd_1771_;
goto v___jp_1780_;
}
v___jp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v_a_1781_);
lean_ctor_set(v___x_1773_, 0, v___x_1779_);
v___x_1783_ = v___x_1773_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_a_1781_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
size_t v___x_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = ((size_t)1ULL);
v___x_1785_ = lean_usize_add(v_i_1762_, v___x_1784_);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1759_, v_as_1760_, v_sz_1761_, v___x_1785_, v___x_1783_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_del_object(v___x_1773_);
lean_dec(v_snd_1771_);
lean_dec_ref(v_goal_1759_);
v_a_1794_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1776_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1776_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1804_, lean_object* v_as_1805_, lean_object* v_sz_1806_, lean_object* v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
size_t v_sz_boxed_1814_; size_t v_i_boxed_1815_; lean_object* v_res_1816_; 
v_sz_boxed_1814_ = lean_unbox_usize(v_sz_1806_);
lean_dec(v_sz_1806_);
v_i_boxed_1815_ = lean_unbox_usize(v_i_1807_);
lean_dec(v_i_1807_);
v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1804_, v_as_1805_, v_sz_boxed_1814_, v_i_boxed_1815_, v_b_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v_as_1805_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1817_, lean_object* v_as_1818_, size_t v_sz_1819_, size_t v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_usize_dec_lt(v_i_1820_, v_sz_1819_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref(v_goal_1817_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_b_1821_);
return v___x_1828_;
}
else
{
lean_object* v_snd_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1860_; 
v_snd_1829_ = lean_ctor_get(v_b_1821_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_b_1821_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_b_1821_, 0);
lean_dec(v_unused_1861_);
v___x_1831_ = v_b_1821_;
v_isShared_1832_ = v_isSharedCheck_1860_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snd_1829_);
lean_dec(v_b_1821_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1860_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_array_uget_borrowed(v_as_1818_, v_i_1820_);
lean_inc(v_a_1833_);
lean_inc_ref(v_goal_1817_);
v___x_1834_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1817_, v_a_1833_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_self_1836_; lean_object* v___x_1837_; lean_object* v_a_1839_; lean_object* v___x_1846_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1834_);
v_self_1836_ = lean_ctor_get(v_a_1835_, 0);
lean_inc_ref(v_self_1836_);
lean_dec(v_a_1835_);
v___x_1837_ = lean_box(0);
lean_inc_ref(v_self_1836_);
v___x_1846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1836_);
if (lean_obj_tag(v___x_1846_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1848_; 
v_val_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_val_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1829_, v_val_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1829_, v_self_1836_);
lean_dec_ref(v_self_1836_);
if (lean_obj_tag(v___x_1849_) == 1)
{
lean_object* v_val_1850_; lean_object* v___x_1851_; 
v_val_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_val_1850_);
lean_dec_ref(v___x_1849_);
lean_inc_ref(v_goal_1817_);
v___x_1851_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1817_, v_val_1847_, v_val_1850_, v_snd_1829_);
v_a_1839_ = v___x_1851_;
goto v___jp_1838_;
}
else
{
lean_dec(v___x_1849_);
lean_dec(v_val_1847_);
v_a_1839_ = v_snd_1829_;
goto v___jp_1838_;
}
}
else
{
lean_dec_ref(v___x_1848_);
lean_dec(v_val_1847_);
lean_dec_ref(v_self_1836_);
v_a_1839_ = v_snd_1829_;
goto v___jp_1838_;
}
}
else
{
lean_dec(v___x_1846_);
lean_dec_ref(v_self_1836_);
v_a_1839_ = v_snd_1829_;
goto v___jp_1838_;
}
v___jp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v_a_1839_);
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1841_ = v___x_1831_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_a_1839_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
size_t v___x_1842_; size_t v___x_1843_; 
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_add(v_i_1820_, v___x_1842_);
v_i_1820_ = v___x_1843_;
v_b_1821_ = v___x_1841_;
goto _start;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_del_object(v___x_1831_);
lean_dec(v_snd_1829_);
lean_dec_ref(v_goal_1817_);
v_a_1852_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1834_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1834_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1862_, lean_object* v_as_1863_, lean_object* v_sz_1864_, lean_object* v_i_1865_, lean_object* v_b_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1864_);
lean_dec(v_sz_1864_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1862_, v_as_1863_, v_sz_boxed_1872_, v_i_boxed_1873_, v_b_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_as_1863_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1875_, lean_object* v_as_1876_, size_t v_sz_1877_, size_t v_i_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; 
lean_dec_ref(v_goal_1875_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_b_1879_);
return v___x_1886_;
}
else
{
lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1918_; 
v_snd_1887_ = lean_ctor_get(v_b_1879_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_b_1879_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v_b_1879_, 0);
lean_dec(v_unused_1919_);
v___x_1889_ = v_b_1879_;
v_isShared_1890_ = v_isSharedCheck_1918_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_dec(v_b_1879_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1918_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
lean_inc(v_a_1891_);
lean_inc_ref(v_goal_1875_);
v___x_1892_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1875_, v_a_1891_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v_self_1894_; lean_object* v___x_1895_; lean_object* v_a_1897_; lean_object* v___x_1904_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v_self_1894_ = lean_ctor_get(v_a_1893_, 0);
lean_inc_ref(v_self_1894_);
lean_dec(v_a_1893_);
v___x_1895_ = lean_box(0);
lean_inc_ref(v_self_1894_);
v___x_1904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1894_);
if (lean_obj_tag(v___x_1904_) == 1)
{
lean_object* v_val_1905_; lean_object* v___x_1906_; 
v_val_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_val_1905_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1887_, v_val_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1887_, v_self_1894_);
lean_dec_ref(v_self_1894_);
if (lean_obj_tag(v___x_1907_) == 1)
{
lean_object* v_val_1908_; lean_object* v___x_1909_; 
v_val_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1908_);
lean_dec_ref(v___x_1907_);
lean_inc_ref(v_goal_1875_);
v___x_1909_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1875_, v_val_1905_, v_val_1908_, v_snd_1887_);
v_a_1897_ = v___x_1909_;
goto v___jp_1896_;
}
else
{
lean_dec(v___x_1907_);
lean_dec(v_val_1905_);
v_a_1897_ = v_snd_1887_;
goto v___jp_1896_;
}
}
else
{
lean_dec_ref(v___x_1906_);
lean_dec(v_val_1905_);
lean_dec_ref(v_self_1894_);
v_a_1897_ = v_snd_1887_;
goto v___jp_1896_;
}
}
else
{
lean_dec(v___x_1904_);
lean_dec_ref(v_self_1894_);
v_a_1897_ = v_snd_1887_;
goto v___jp_1896_;
}
v___jp_1896_:
{
lean_object* v___x_1899_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_a_1897_);
lean_ctor_set(v___x_1889_, 0, v___x_1895_);
v___x_1899_ = v___x_1889_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1897_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1878_, v___x_1900_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1875_, v_as_1876_, v_sz_1877_, v___x_1901_, v___x_1899_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1902_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1889_);
lean_dec(v_snd_1887_);
lean_dec_ref(v_goal_1875_);
v_a_1910_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1892_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1892_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1920_, lean_object* v_as_1921_, lean_object* v_sz_1922_, lean_object* v_i_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
size_t v_sz_boxed_1930_; size_t v_i_boxed_1931_; lean_object* v_res_1932_; 
v_sz_boxed_1930_ = lean_unbox_usize(v_sz_1922_);
lean_dec(v_sz_1922_);
v_i_boxed_1931_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1920_, v_as_1921_, v_sz_boxed_1930_, v_i_boxed_1931_, v_b_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec_ref(v_as_1921_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_goal_1933_, lean_object* v_inh_1934_, lean_object* v_n_1935_, lean_object* v_b_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
if (lean_obj_tag(v_n_1935_) == 0)
{
lean_object* v_cs_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1976_; 
v_cs_1942_ = lean_ctor_get(v_n_1935_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_n_1935_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1944_ = v_n_1935_;
v_isShared_1945_ = v_isSharedCheck_1976_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_cs_1942_);
lean_dec(v_n_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1976_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; size_t v_sz_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_b_1936_);
v_sz_1948_ = lean_array_size(v_cs_1942_);
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_goal_1933_, v_inh_1934_, v_cs_1942_, v_sz_1948_, v___x_1949_, v___x_1947_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec_ref(v_cs_1942_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1967_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1967_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1967_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v_fst_1955_; 
v_fst_1955_ = lean_ctor_get(v_a_1951_, 0);
if (lean_obj_tag(v_fst_1955_) == 0)
{
lean_object* v_snd_1956_; lean_object* v___x_1958_; 
v_snd_1956_ = lean_ctor_get(v_a_1951_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_a_1951_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 1);
lean_ctor_set(v___x_1944_, 0, v_snd_1956_);
v___x_1958_ = v___x_1944_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_snd_1956_);
v___x_1958_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1958_);
v___x_1960_ = v___x_1953_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_val_1963_; lean_object* v___x_1965_; 
lean_inc_ref(v_fst_1955_);
lean_dec(v_a_1951_);
lean_del_object(v___x_1944_);
v_val_1963_ = lean_ctor_get(v_fst_1955_, 0);
lean_inc(v_val_1963_);
lean_dec_ref(v_fst_1955_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_val_1963_);
v___x_1965_ = v___x_1953_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_val_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1944_);
v_a_1968_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1950_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1950_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_vs_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2011_; 
v_vs_1977_ = lean_ctor_get(v_n_1935_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_n_1935_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1979_ = v_n_1935_;
v_isShared_1980_ = v_isSharedCheck_2011_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_vs_1977_);
lean_dec(v_n_1935_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2011_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; size_t v_sz_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_b_1936_);
v_sz_1983_ = lean_array_size(v_vs_1977_);
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1933_, v_vs_1977_, v_sz_1983_, v___x_1984_, v___x_1982_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec_ref(v_vs_1977_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2002_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2002_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2002_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_fst_1990_; 
v_fst_1990_ = lean_ctor_get(v_a_1986_, 0);
if (lean_obj_tag(v_fst_1990_) == 0)
{
lean_object* v_snd_1991_; lean_object* v___x_1993_; 
v_snd_1991_ = lean_ctor_get(v_a_1986_, 1);
lean_inc(v_snd_1991_);
lean_dec(v_a_1986_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v_snd_1991_);
v___x_1993_ = v___x_1979_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_snd_1991_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1993_);
v___x_1995_ = v___x_1988_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_val_1998_; lean_object* v___x_2000_; 
lean_inc_ref(v_fst_1990_);
lean_dec(v_a_1986_);
lean_del_object(v___x_1979_);
v_val_1998_ = lean_ctor_get(v_fst_1990_, 0);
lean_inc(v_val_1998_);
lean_dec_ref(v_fst_1990_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_val_1998_);
v___x_2000_ = v___x_1988_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_val_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1979_);
v_a_2003_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1985_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1985_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_goal_2012_, lean_object* v_inh_2013_, lean_object* v_as_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec_ref(v_goal_2012_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_b_2017_);
return v___x_2024_;
}
else
{
lean_object* v_snd_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2059_; 
v_snd_2025_ = lean_ctor_get(v_b_2017_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_b_2017_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_b_2017_, 0);
lean_dec(v_unused_2060_);
v___x_2027_ = v_b_2017_;
v_isShared_2028_ = v_isSharedCheck_2059_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_snd_2025_);
lean_dec(v_b_2017_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2059_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_array_uget_borrowed(v_as_2014_, v_i_2016_);
lean_inc(v_snd_2025_);
lean_inc(v_a_2029_);
lean_inc_ref(v_goal_2012_);
v___x_2030_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_goal_2012_, v_inh_2013_, v_a_2029_, v_snd_2025_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2050_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2050_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2050_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
if (lean_obj_tag(v_a_2031_) == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec_ref(v_goal_2012_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2031_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2035_);
v___x_2037_ = v___x_2027_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_snd_2025_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
lean_del_object(v___x_2033_);
lean_dec(v_snd_2025_);
v_a_2042_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v_a_2031_);
v___x_2043_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_a_2042_);
lean_ctor_set(v___x_2027_, 0, v___x_2043_);
v___x_2045_ = v___x_2027_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2042_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2016_, v___x_2046_);
v_i_2016_ = v___x_2047_;
v_b_2017_ = v___x_2045_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2027_);
lean_dec(v_snd_2025_);
lean_dec_ref(v_goal_2012_);
v_a_2051_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2030_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2030_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_goal_2061_, lean_object* v_inh_2062_, lean_object* v_as_2063_, lean_object* v_sz_2064_, lean_object* v_i_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
size_t v_sz_boxed_2072_; size_t v_i_boxed_2073_; lean_object* v_res_2074_; 
v_sz_boxed_2072_ = lean_unbox_usize(v_sz_2064_);
lean_dec(v_sz_2064_);
v_i_boxed_2073_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_goal_2061_, v_inh_2062_, v_as_2063_, v_sz_boxed_2072_, v_i_boxed_2073_, v_b_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec_ref(v_as_2063_);
lean_dec_ref(v_inh_2062_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_2075_, lean_object* v_inh_2076_, lean_object* v_n_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_goal_2075_, v_inh_2076_, v_n_2077_, v_b_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_inh_2076_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2085_, lean_object* v_t_2086_, lean_object* v_init_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_root_2093_; lean_object* v_tail_2094_; lean_object* v___x_2095_; 
v_root_2093_ = lean_ctor_get(v_t_2086_, 0);
lean_inc_ref(v_root_2093_);
v_tail_2094_ = lean_ctor_get(v_t_2086_, 1);
lean_inc_ref(v_tail_2094_);
lean_dec_ref(v_t_2086_);
lean_inc_ref(v_init_2087_);
lean_inc_ref(v_goal_2085_);
v___x_2095_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_goal_2085_, v_init_2087_, v_root_2093_, v_init_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec_ref(v_init_2087_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2132_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2132_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2132_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
if (lean_obj_tag(v_a_2096_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; 
lean_dec_ref(v_tail_2094_);
lean_dec_ref(v_goal_2085_);
v_a_2100_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v_a_2096_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_a_2100_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; size_t v_sz_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
lean_del_object(v___x_2098_);
v_a_2104_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v_a_2096_);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_a_2104_);
v_sz_2107_ = lean_array_size(v_tail_2094_);
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2085_, v_tail_2094_, v_sz_2107_, v___x_2108_, v___x_2106_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec_ref(v_tail_2094_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2123_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2123_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2123_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_fst_2114_; 
v_fst_2114_ = lean_ctor_get(v_a_2110_, 0);
if (lean_obj_tag(v_fst_2114_) == 0)
{
lean_object* v_snd_2115_; lean_object* v___x_2117_; 
v_snd_2115_ = lean_ctor_get(v_a_2110_, 1);
lean_inc(v_snd_2115_);
lean_dec(v_a_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_snd_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_snd_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
else
{
lean_object* v_val_2119_; lean_object* v___x_2121_; 
lean_inc_ref(v_fst_2114_);
lean_dec(v_a_2110_);
v_val_2119_ = lean_ctor_get(v_fst_2114_, 0);
lean_inc(v_val_2119_);
lean_dec_ref(v_fst_2114_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_val_2119_);
v___x_2121_ = v___x_2112_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_val_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2109_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2109_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_tail_2094_);
lean_dec_ref(v_goal_2085_);
v_a_2133_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2095_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2095_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2141_, lean_object* v_t_2142_, lean_object* v_init_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2141_, v_t_2142_, v_init_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2149_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_unsigned_to_nat(16u);
v___x_2152_ = lean_mk_array(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_model_2155_; 
v___x_2153_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2154_ = lean_unsigned_to_nat(0u);
v_model_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2155_, 0, v___x_2154_);
lean_ctor_set(v_model_2155_, 1, v___x_2153_);
return v_model_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2163_, lean_object* v_structId_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2171_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2170_, v_goal_2163_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_toGoalState_2173_; lean_object* v_structs_2174_; lean_object* v_exprs_2175_; lean_object* v___x_2176_; lean_object* v_model_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v_toGoalState_2173_ = lean_ctor_get(v_goal_2163_, 0);
v_structs_2174_ = lean_ctor_get(v_a_2172_, 0);
lean_inc_ref(v_structs_2174_);
lean_dec(v_a_2172_);
v_exprs_2175_ = lean_ctor_get(v_toGoalState_2173_, 3);
v___x_2176_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2178_ = lean_array_get(v___x_2176_, v_structs_2174_, v_structId_2164_);
lean_dec_ref(v_structs_2174_);
lean_inc(v_a_2168_);
lean_inc_ref(v_a_2167_);
lean_inc(v_a_2166_);
lean_inc_ref(v_a_2165_);
lean_inc_ref(v_exprs_2175_);
lean_inc(v___x_2178_);
lean_inc_ref(v_goal_2163_);
v___x_2179_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2163_, v___x_2178_, v_exprs_2175_, v_model_2177_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
lean_inc(v_a_2168_);
lean_inc_ref(v_a_2167_);
lean_inc(v_a_2166_);
lean_inc_ref(v_a_2165_);
lean_inc_ref(v_goal_2163_);
v___x_2181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2163_, v_structId_2164_, v_a_2180_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
lean_inc_ref(v_exprs_2175_);
lean_inc_ref(v_goal_2163_);
v___x_2183_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2163_, v_exprs_2175_, v_a_2182_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_type_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2183_);
v_type_2185_ = lean_ctor_get(v___x_2178_, 2);
lean_inc_ref(v_type_2185_);
lean_dec(v___x_2178_);
v___x_2186_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2186_, 0, v_type_2185_);
lean_inc(v_a_2168_);
lean_inc_ref(v_a_2167_);
lean_inc(v_a_2166_);
lean_inc_ref(v_a_2165_);
v___x_2187_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2163_, v___x_2186_, v_a_2184_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2190_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2189_, v_a_2188_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v___x_2190_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v___x_2190_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_a_2188_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2188_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2188_);
v_a_2199_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2190_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2190_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v___x_2187_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v___x_2178_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_goal_2163_);
v_a_2207_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2183_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2183_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v___x_2178_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_goal_2163_);
v_a_2215_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2181_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2181_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v___x_2178_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_goal_2163_);
v_a_2223_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2179_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2179_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
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
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2168_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_goal_2163_);
v_a_2231_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2233_ = v___x_2171_;
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2171_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_ref_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v_ref_2235_ = lean_ctor_get(v_a_2167_, 5);
lean_inc(v_ref_2235_);
lean_dec_ref(v_a_2167_);
v___x_2236_ = lean_io_error_to_string(v_a_2231_);
v___x_2237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_ofFormat(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_ref_2235_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2239_);
v___x_2241_ = v___x_2233_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2244_, lean_object* v_structId_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2244_, v_structId_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_structId_2245_);
return v_res_2251_;
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

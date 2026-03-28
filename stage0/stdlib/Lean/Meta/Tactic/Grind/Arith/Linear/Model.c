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
lean_dec_ref(v_assignment_71_);
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
lean_object* v_self_132_; lean_object* v___x_133_; uint8_t v_foApprox_134_; uint8_t v_ctxApprox_135_; uint8_t v_quasiPatternApprox_136_; uint8_t v_constApprox_137_; uint8_t v_isDefEqStuckEx_138_; uint8_t v_unificationHints_139_; uint8_t v_proofIrrelevance_140_; uint8_t v_assignSyntheticOpaque_141_; uint8_t v_offsetCnstrs_142_; uint8_t v_etaStruct_143_; uint8_t v_univApprox_144_; uint8_t v_iota_145_; uint8_t v_beta_146_; uint8_t v_proj_147_; uint8_t v_zeta_148_; uint8_t v_zetaDelta_149_; uint8_t v_zetaUnused_150_; uint8_t v_zetaHave_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_188_; 
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
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_188_ == 0)
{
v___x_153_ = v___x_133_;
v_isShared_154_ = v_isSharedCheck_188_;
goto v_resetjp_152_;
}
else
{
lean_dec(v___x_133_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_188_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v_trackZetaDelta_155_; lean_object* v_zetaDeltaSet_156_; lean_object* v_lctx_157_; lean_object* v_localInstances_158_; lean_object* v_defEqCtx_x3f_159_; lean_object* v_synthPendingDepth_160_; lean_object* v_canUnfold_x3f_161_; uint8_t v_univApprox_162_; uint8_t v_inTypeClassResolution_163_; uint8_t v_cacheInferType_164_; uint8_t v___x_165_; lean_object* v_config_167_; 
v_trackZetaDelta_155_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7);
v_zetaDeltaSet_156_ = lean_ctor_get(v_a_127_, 1);
v_lctx_157_ = lean_ctor_get(v_a_127_, 2);
v_localInstances_158_ = lean_ctor_get(v_a_127_, 3);
v_defEqCtx_x3f_159_ = lean_ctor_get(v_a_127_, 4);
v_synthPendingDepth_160_ = lean_ctor_get(v_a_127_, 5);
v_canUnfold_x3f_161_ = lean_ctor_get(v_a_127_, 6);
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
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 0, v_foApprox_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 1, v_ctxApprox_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 2, v_quasiPatternApprox_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 3, v_constApprox_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 4, v_isDefEqStuckEx_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 5, v_unificationHints_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 6, v_proofIrrelevance_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 7, v_assignSyntheticOpaque_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 8, v_offsetCnstrs_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 10, v_etaStruct_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 11, v_univApprox_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 12, v_iota_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 13, v_beta_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 14, v_proj_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 15, v_zeta_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 16, v_zetaDelta_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 17, v_zetaUnused_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, 18, v_zetaHave_151_);
v_config_167_ = v_reuseFailAlloc_187_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v_key_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_ctor_set_uint8(v_config_167_, 9, v___x_165_);
v___x_168_ = l_Lean_Meta_Context_configKey(v_a_127_);
v___x_169_ = 2ULL;
v___x_170_ = lean_uint64_shift_right(v___x_168_, v___x_169_);
v___x_171_ = lean_uint64_shift_left(v___x_170_, v___x_169_);
v___x_172_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
v_key_173_ = lean_uint64_lor(v___x_171_, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_174_, 0, v_config_167_);
lean_ctor_set_uint64(v___x_174_, sizeof(void*)*1, v_key_173_);
lean_inc(v_canUnfold_x3f_161_);
lean_inc(v_synthPendingDepth_160_);
lean_inc(v_defEqCtx_x3f_159_);
lean_inc_ref(v_localInstances_158_);
lean_inc_ref(v_lctx_157_);
lean_inc(v_zetaDeltaSet_156_);
v___x_175_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_zetaDeltaSet_156_);
lean_ctor_set(v___x_175_, 2, v_lctx_157_);
lean_ctor_set(v___x_175_, 3, v_localInstances_158_);
lean_ctor_set(v___x_175_, 4, v_defEqCtx_x3f_159_);
lean_ctor_set(v___x_175_, 5, v_synthPendingDepth_160_);
lean_ctor_set(v___x_175_, 6, v_canUnfold_x3f_161_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7, v_trackZetaDelta_155_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 1, v_univApprox_162_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 2, v_inTypeClassResolution_163_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 3, v_cacheInferType_164_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_175_);
v___x_176_ = lean_infer_type(v_self_132_, v___x_175_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_176_);
v___x_178_ = l_Lean_Meta_isExprDefEq(v_a_177_, v_type_125_, v___x_175_, v_a_128_, v_a_129_, v_a_130_);
lean_dec_ref(v___x_175_);
return v___x_178_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v___x_175_);
lean_dec_ref(v_type_125_);
v_a_179_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_176_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
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
lean_dec_ref(v___x_354_);
v_val_356_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_val_356_);
lean_dec_ref(v_a_355_);
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
lean_dec_ref(v___x_379_);
v_val_381_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref(v_a_380_);
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
lean_dec_ref(v___x_404_);
v_val_406_ = lean_ctor_get(v_a_405_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v_a_405_);
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
lean_dec_ref(v_a_431_);
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
lean_dec_ref(v_a_470_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v___x_652_, lean_object* v_goal_653_, lean_object* v_structId_654_, lean_object* v_as_655_, size_t v_sz_656_, size_t v_i_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_657_, v_sz_656_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_goal_653_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_b_658_);
return v___x_665_;
}
else
{
lean_object* v_snd_666_; lean_object* v_a_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_698_; 
v_snd_666_ = lean_ctor_get(v_b_658_, 1);
lean_inc(v_snd_666_);
lean_dec_ref(v_b_658_);
v_a_667_ = lean_array_uget(v_as_655_, v_i_657_);
v_fst_668_ = lean_ctor_get(v_a_667_, 0);
v_snd_669_ = lean_ctor_get(v_a_667_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_698_ == 0)
{
v___x_671_ = v_a_667_;
v_isShared_672_ = v_isSharedCheck_698_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_a_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_698_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_a_675_; uint8_t v___y_683_; uint8_t v___x_696_; 
v___x_673_ = lean_box(0);
v___x_696_ = lean_nat_dec_eq(v_structId_654_, v_snd_669_);
lean_dec(v_snd_669_);
if (v___x_696_ == 0)
{
v___y_683_ = v___x_696_;
goto v___jp_682_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_666_, v_fst_668_);
if (v___x_697_ == 0)
{
v___y_683_ = v___x_696_;
goto v___jp_682_;
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
v___jp_682_:
{
if (v___y_683_ == 0)
{
lean_dec(v_fst_668_);
v_a_675_ = v_snd_666_;
goto v___jp_674_;
}
else
{
lean_object* v___x_684_; 
lean_inc(v_fst_668_);
v___x_684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_652_, v_snd_666_, v_fst_668_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
if (lean_obj_tag(v_a_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref(v_a_685_);
lean_inc_ref(v_goal_653_);
v___x_687_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_653_, v_fst_668_, v_val_686_, v_snd_666_);
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
lean_dec_ref(v_goal_653_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v___x_699_, lean_object* v_goal_700_, lean_object* v_structId_701_, lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
size_t v_sz_boxed_711_; size_t v_i_boxed_712_; lean_object* v_res_713_; 
v_sz_boxed_711_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_712_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_699_, v_goal_700_, v_structId_701_, v_as_702_, v_sz_boxed_711_, v_i_boxed_712_, v_b_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_as_702_);
lean_dec(v_structId_701_);
lean_dec_ref(v___x_699_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v___x_714_, lean_object* v_goal_715_, lean_object* v_structId_716_, lean_object* v_as_717_, size_t v_sz_718_, size_t v_i_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_goal_715_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_720_);
return v___x_727_;
}
else
{
lean_object* v_snd_728_; lean_object* v_a_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_760_; 
v_snd_728_ = lean_ctor_get(v_b_720_, 1);
lean_inc(v_snd_728_);
lean_dec_ref(v_b_720_);
v_a_729_ = lean_array_uget(v_as_717_, v_i_719_);
v_fst_730_ = lean_ctor_get(v_a_729_, 0);
v_snd_731_ = lean_ctor_get(v_a_729_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_760_ == 0)
{
v___x_733_ = v_a_729_;
v_isShared_734_ = v_isSharedCheck_760_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_dec(v_a_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_760_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v_a_737_; uint8_t v___y_745_; uint8_t v___x_758_; 
v___x_735_ = lean_box(0);
v___x_758_ = lean_nat_dec_eq(v_structId_716_, v_snd_731_);
lean_dec(v_snd_731_);
if (v___x_758_ == 0)
{
v___y_745_ = v___x_758_;
goto v___jp_744_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_728_, v_fst_730_);
if (v___x_759_ == 0)
{
v___y_745_ = v___x_758_;
goto v___jp_744_;
}
else
{
lean_dec(v_fst_730_);
v_a_737_ = v_snd_728_;
goto v___jp_736_;
}
}
v___jp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_737_);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_a_737_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_add(v_i_719_, v___x_740_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_714_, v_goal_715_, v_structId_716_, v_as_717_, v_sz_718_, v___x_741_, v___x_739_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_742_;
}
}
v___jp_744_:
{
if (v___y_745_ == 0)
{
lean_dec(v_fst_730_);
v_a_737_ = v_snd_728_;
goto v___jp_736_;
}
else
{
lean_object* v___x_746_; 
lean_inc(v_fst_730_);
v___x_746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_714_, v_snd_728_, v_fst_730_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
if (lean_obj_tag(v_a_747_) == 1)
{
lean_object* v_val_748_; lean_object* v___x_749_; 
v_val_748_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_val_748_);
lean_dec_ref(v_a_747_);
lean_inc_ref(v_goal_715_);
v___x_749_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_715_, v_fst_730_, v_val_748_, v_snd_728_);
v_a_737_ = v___x_749_;
goto v___jp_736_;
}
else
{
lean_dec(v_a_747_);
lean_dec(v_fst_730_);
v_a_737_ = v_snd_728_;
goto v___jp_736_;
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_del_object(v___x_733_);
lean_dec(v_fst_730_);
lean_dec(v_snd_728_);
lean_dec_ref(v_goal_715_);
v_a_750_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_746_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_746_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v___x_761_, lean_object* v_goal_762_, lean_object* v_structId_763_, lean_object* v_as_764_, lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
size_t v_sz_boxed_773_; size_t v_i_boxed_774_; lean_object* v_res_775_; 
v_sz_boxed_773_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_774_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_761_, v_goal_762_, v_structId_763_, v_as_764_, v_sz_boxed_773_, v_i_boxed_774_, v_b_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_as_764_);
lean_dec(v_structId_763_);
lean_dec_ref(v___x_761_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_776_, lean_object* v___x_777_, lean_object* v_goal_778_, lean_object* v_structId_779_, lean_object* v_n_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
if (lean_obj_tag(v_n_780_) == 0)
{
lean_object* v_cs_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_821_; 
v_cs_787_ = lean_ctor_get(v_n_780_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_n_780_);
if (v_isSharedCheck_821_ == 0)
{
v___x_789_ = v_n_780_;
v_isShared_790_ = v_isSharedCheck_821_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_cs_787_);
lean_dec(v_n_780_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_821_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; size_t v_sz_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_b_781_);
v_sz_793_ = lean_array_size(v_cs_787_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_776_, v___x_777_, v_goal_778_, v_structId_779_, v_cs_787_, v_sz_793_, v___x_794_, v___x_792_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec_ref(v_cs_787_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_812_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_812_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_812_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; 
v_fst_800_ = lean_ctor_get(v_a_796_, 0);
if (lean_obj_tag(v_fst_800_) == 0)
{
lean_object* v_snd_801_; lean_object* v___x_803_; 
v_snd_801_ = lean_ctor_get(v_a_796_, 1);
lean_inc(v_snd_801_);
lean_dec(v_a_796_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 0, v_snd_801_);
v___x_803_ = v___x_789_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_snd_801_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_803_);
v___x_805_ = v___x_798_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_val_808_; lean_object* v___x_810_; 
lean_inc_ref(v_fst_800_);
lean_dec(v_a_796_);
lean_del_object(v___x_789_);
v_val_808_ = lean_ctor_get(v_fst_800_, 0);
lean_inc(v_val_808_);
lean_dec_ref(v_fst_800_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_val_808_);
v___x_810_ = v___x_798_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_val_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_del_object(v___x_789_);
v_a_813_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_795_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_795_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
else
{
lean_object* v_vs_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_856_; 
v_vs_822_ = lean_ctor_get(v_n_780_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_n_780_);
if (v_isSharedCheck_856_ == 0)
{
v___x_824_ = v_n_780_;
v_isShared_825_ = v_isSharedCheck_856_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_vs_822_);
lean_dec(v_n_780_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_856_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; size_t v_sz_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_b_781_);
v_sz_828_ = lean_array_size(v_vs_822_);
v___x_829_ = ((size_t)0ULL);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_777_, v_goal_778_, v_structId_779_, v_vs_822_, v_sz_828_, v___x_829_, v___x_827_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec_ref(v_vs_822_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_847_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_847_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_847_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_fst_835_; 
v_fst_835_ = lean_ctor_get(v_a_831_, 0);
if (lean_obj_tag(v_fst_835_) == 0)
{
lean_object* v_snd_836_; lean_object* v___x_838_; 
v_snd_836_ = lean_ctor_get(v_a_831_, 1);
lean_inc(v_snd_836_);
lean_dec(v_a_831_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_snd_836_);
v___x_838_ = v___x_824_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_snd_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_838_);
v___x_840_ = v___x_833_;
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
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; 
lean_inc_ref(v_fst_835_);
lean_dec(v_a_831_);
lean_del_object(v___x_824_);
v_val_843_ = lean_ctor_get(v_fst_835_, 0);
lean_inc(v_val_843_);
lean_dec_ref(v_fst_835_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_val_843_);
v___x_845_ = v___x_833_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_val_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_824_);
v_a_848_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_830_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_830_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_857_, lean_object* v___x_858_, lean_object* v_goal_859_, lean_object* v_structId_860_, lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec_ref(v_goal_859_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_b_864_);
return v___x_871_;
}
else
{
lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_906_; 
v_snd_872_ = lean_ctor_get(v_b_864_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_b_864_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_b_864_, 0);
lean_dec(v_unused_907_);
v___x_874_ = v_b_864_;
v_isShared_875_ = v_isSharedCheck_906_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_dec(v_b_864_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_906_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_array_uget_borrowed(v_as_861_, v_i_863_);
lean_inc(v_snd_872_);
lean_inc(v_a_876_);
lean_inc_ref(v_goal_859_);
v___x_877_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_857_, v___x_858_, v_goal_859_, v_structId_860_, v_a_876_, v_snd_872_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_897_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_897_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_897_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_897_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (lean_obj_tag(v_a_878_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec_ref(v_goal_859_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_a_878_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_snd_872_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_del_object(v___x_880_);
lean_dec(v_snd_872_);
v_a_889_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v_a_878_);
v___x_890_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v_a_889_);
lean_ctor_set(v___x_874_, 0, v___x_890_);
v___x_892_ = v___x_874_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_889_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
size_t v___x_893_; size_t v___x_894_; 
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_i_863_, v___x_893_);
v_i_863_ = v___x_894_;
v_b_864_ = v___x_892_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec_ref(v_goal_859_);
v_a_898_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_877_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_877_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_908_, lean_object* v___x_909_, lean_object* v_goal_910_, lean_object* v_structId_911_, lean_object* v_as_912_, lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
size_t v_sz_boxed_921_; size_t v_i_boxed_922_; lean_object* v_res_923_; 
v_sz_boxed_921_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_922_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_908_, v___x_909_, v_goal_910_, v_structId_911_, v_as_912_, v_sz_boxed_921_, v_i_boxed_922_, v_b_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_as_912_);
lean_dec(v_structId_911_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v_init_908_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_924_, lean_object* v___x_925_, lean_object* v_goal_926_, lean_object* v_structId_927_, lean_object* v_n_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_924_, v___x_925_, v_goal_926_, v_structId_927_, v_n_928_, v_b_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v_structId_927_);
lean_dec_ref(v___x_925_);
lean_dec_ref(v_init_924_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v___x_936_, lean_object* v_goal_937_, lean_object* v_structId_938_, lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_941_, v_sz_940_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_goal_937_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_942_);
return v___x_949_;
}
else
{
lean_object* v_snd_950_; lean_object* v_a_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_982_; 
v_snd_950_ = lean_ctor_get(v_b_942_, 1);
lean_inc(v_snd_950_);
lean_dec_ref(v_b_942_);
v_a_951_ = lean_array_uget(v_as_939_, v_i_941_);
v_fst_952_ = lean_ctor_get(v_a_951_, 0);
v_snd_953_ = lean_ctor_get(v_a_951_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_955_ = v_a_951_;
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_dec(v_a_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_a_959_; uint8_t v___y_967_; uint8_t v___x_980_; 
v___x_957_ = lean_box(0);
v___x_980_ = lean_nat_dec_eq(v_structId_938_, v_snd_953_);
lean_dec(v_snd_953_);
if (v___x_980_ == 0)
{
v___y_967_ = v___x_980_;
goto v___jp_966_;
}
else
{
uint8_t v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_950_, v_fst_952_);
if (v___x_981_ == 0)
{
v___y_967_ = v___x_980_;
goto v___jp_966_;
}
else
{
lean_dec(v_fst_952_);
v_a_959_ = v_snd_950_;
goto v___jp_958_;
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_a_959_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_941_, v___x_962_);
v_i_941_ = v___x_963_;
v_b_942_ = v___x_961_;
goto _start;
}
}
v___jp_966_:
{
if (v___y_967_ == 0)
{
lean_dec(v_fst_952_);
v_a_959_ = v_snd_950_;
goto v___jp_958_;
}
else
{
lean_object* v___x_968_; 
lean_inc(v_fst_952_);
v___x_968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_936_, v_snd_950_, v_fst_952_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
if (lean_obj_tag(v_a_969_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_971_; 
v_val_970_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref(v_a_969_);
lean_inc_ref(v_goal_937_);
v___x_971_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_937_, v_fst_952_, v_val_970_, v_snd_950_);
v_a_959_ = v___x_971_;
goto v___jp_958_;
}
else
{
lean_dec(v_a_969_);
lean_dec(v_fst_952_);
v_a_959_ = v_snd_950_;
goto v___jp_958_;
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_del_object(v___x_955_);
lean_dec(v_fst_952_);
lean_dec(v_snd_950_);
lean_dec_ref(v_goal_937_);
v_a_972_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_968_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_968_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v___x_983_, lean_object* v_goal_984_, lean_object* v_structId_985_, lean_object* v_as_986_, lean_object* v_sz_987_, lean_object* v_i_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
size_t v_sz_boxed_995_; size_t v_i_boxed_996_; lean_object* v_res_997_; 
v_sz_boxed_995_ = lean_unbox_usize(v_sz_987_);
lean_dec(v_sz_987_);
v_i_boxed_996_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_983_, v_goal_984_, v_structId_985_, v_as_986_, v_sz_boxed_995_, v_i_boxed_996_, v_b_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_as_986_);
lean_dec(v_structId_985_);
lean_dec_ref(v___x_983_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v___x_998_, lean_object* v_goal_999_, lean_object* v_structId_1000_, lean_object* v_as_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_b_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec_ref(v_goal_999_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_b_1004_);
return v___x_1011_;
}
else
{
lean_object* v_snd_1012_; lean_object* v_a_1013_; lean_object* v_fst_1014_; lean_object* v_snd_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1044_; 
v_snd_1012_ = lean_ctor_get(v_b_1004_, 1);
lean_inc(v_snd_1012_);
lean_dec_ref(v_b_1004_);
v_a_1013_ = lean_array_uget(v_as_1001_, v_i_1003_);
v_fst_1014_ = lean_ctor_get(v_a_1013_, 0);
v_snd_1015_ = lean_ctor_get(v_a_1013_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1017_ = v_a_1013_;
v_isShared_1018_ = v_isSharedCheck_1044_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_snd_1015_);
lean_inc(v_fst_1014_);
lean_dec(v_a_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1044_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v_a_1021_; uint8_t v___y_1029_; uint8_t v___x_1042_; 
v___x_1019_ = lean_box(0);
v___x_1042_ = lean_nat_dec_eq(v_structId_1000_, v_snd_1015_);
lean_dec(v_snd_1015_);
if (v___x_1042_ == 0)
{
v___y_1029_ = v___x_1042_;
goto v___jp_1028_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_1012_, v_fst_1014_);
if (v___x_1043_ == 0)
{
v___y_1029_ = v___x_1042_;
goto v___jp_1028_;
}
else
{
lean_dec(v_fst_1014_);
v_a_1021_ = v_snd_1012_;
goto v___jp_1020_;
}
}
v___jp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v_a_1021_);
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_a_1021_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_add(v_i_1003_, v___x_1024_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_998_, v_goal_999_, v_structId_1000_, v_as_1001_, v_sz_1002_, v___x_1025_, v___x_1023_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1026_;
}
}
v___jp_1028_:
{
if (v___y_1029_ == 0)
{
lean_dec(v_fst_1014_);
v_a_1021_ = v_snd_1012_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1030_; 
lean_inc(v_fst_1014_);
v___x_1030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_998_, v_snd_1012_, v_fst_1014_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
if (lean_obj_tag(v_a_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
v_val_1032_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref(v_a_1031_);
lean_inc_ref(v_goal_999_);
v___x_1033_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_999_, v_fst_1014_, v_val_1032_, v_snd_1012_);
v_a_1021_ = v___x_1033_;
goto v___jp_1020_;
}
else
{
lean_dec(v_a_1031_);
lean_dec(v_fst_1014_);
v_a_1021_ = v_snd_1012_;
goto v___jp_1020_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_del_object(v___x_1017_);
lean_dec(v_fst_1014_);
lean_dec(v_snd_1012_);
lean_dec_ref(v_goal_999_);
v_a_1034_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1030_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v___x_1045_, lean_object* v_goal_1046_, lean_object* v_structId_1047_, lean_object* v_as_1048_, lean_object* v_sz_1049_, lean_object* v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1049_);
lean_dec(v_sz_1049_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1045_, v_goal_1046_, v_structId_1047_, v_as_1048_, v_sz_boxed_1057_, v_i_boxed_1058_, v_b_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_as_1048_);
lean_dec(v_structId_1047_);
lean_dec_ref(v___x_1045_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1060_, lean_object* v_goal_1061_, lean_object* v_structId_1062_, lean_object* v_t_1063_, lean_object* v_init_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_root_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; 
v_root_1070_ = lean_ctor_get(v_t_1063_, 0);
lean_inc_ref(v_root_1070_);
v_tail_1071_ = lean_ctor_get(v_t_1063_, 1);
lean_inc_ref(v_tail_1071_);
lean_dec_ref(v_t_1063_);
lean_inc_ref(v_goal_1061_);
lean_inc_ref(v_init_1064_);
v___x_1072_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1064_, v___x_1060_, v_goal_1061_, v_structId_1062_, v_root_1070_, v_init_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v_init_1064_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1109_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1109_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1109_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
if (lean_obj_tag(v_a_1073_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; 
lean_dec_ref(v_tail_1071_);
lean_dec_ref(v_goal_1061_);
v_a_1077_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_a_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; size_t v_sz_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
lean_del_object(v___x_1075_);
v_a_1081_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v_a_1073_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_a_1081_);
v_sz_1084_ = lean_array_size(v_tail_1071_);
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1060_, v_goal_1061_, v_structId_1062_, v_tail_1071_, v_sz_1084_, v___x_1085_, v___x_1083_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v_tail_1071_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1100_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_fst_1091_; 
v_fst_1091_ = lean_ctor_get(v_a_1087_, 0);
if (lean_obj_tag(v_fst_1091_) == 0)
{
lean_object* v_snd_1092_; lean_object* v___x_1094_; 
v_snd_1092_ = lean_ctor_get(v_a_1087_, 1);
lean_inc(v_snd_1092_);
lean_dec(v_a_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_snd_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_snd_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v_val_1096_; lean_object* v___x_1098_; 
lean_inc_ref(v_fst_1091_);
lean_dec(v_a_1087_);
v_val_1096_ = lean_ctor_get(v_fst_1091_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v_fst_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_val_1096_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_val_1096_);
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
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1086_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1086_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_tail_1071_);
lean_dec_ref(v_goal_1061_);
v_a_1110_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1072_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1072_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1118_, lean_object* v_goal_1119_, lean_object* v_structId_1120_, lean_object* v_t_1121_, lean_object* v_init_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1118_, v_goal_1119_, v_structId_1120_, v_t_1121_, v_init_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v_structId_1120_);
lean_dec_ref(v___x_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1129_, lean_object* v_structId_1130_, lean_object* v_model_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1137_, v_goal_1129_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_structs_1140_; lean_object* v_exprToStructIdEntries_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v_structs_1140_ = lean_ctor_get(v_a_1139_, 0);
lean_inc_ref(v_structs_1140_);
v_exprToStructIdEntries_1141_ = lean_ctor_get(v_a_1139_, 3);
lean_inc_ref(v_exprToStructIdEntries_1141_);
lean_dec(v_a_1139_);
v___x_1142_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1143_ = lean_array_get(v___x_1142_, v_structs_1140_, v_structId_1130_);
lean_dec_ref(v_structs_1140_);
v___x_1144_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1143_, v_goal_1129_, v_structId_1130_, v_exprToStructIdEntries_1141_, v_model_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_model_1131_);
lean_dec_ref(v_goal_1129_);
v_a_1145_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1147_ = v___x_1138_;
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_ref_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v_ref_1149_ = lean_ctor_get(v_a_1134_, 5);
v___x_1150_ = lean_io_error_to_string(v_a_1145_);
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_ofFormat(v___x_1151_);
lean_inc(v_ref_1149_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_ref_1149_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1153_);
v___x_1155_ = v___x_1147_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1158_, lean_object* v_structId_1159_, lean_object* v_model_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1158_, v_structId_1159_, v_model_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_structId_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1168_, v_a_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1171_, lean_object* v_m_1172_, lean_object* v_a_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1171_, v_m_1172_, v_a_1173_);
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_m_1172_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1176_, lean_object* v_a_1177_, lean_object* v_x_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1180_, lean_object* v_a_1181_, lean_object* v_x_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1180_, v_a_1181_, v_x_1182_);
lean_dec(v_x_1182_);
lean_dec_ref(v_a_1181_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1185_, lean_object* v___x_1186_, lean_object* v_as_1187_, size_t v_sz_1188_, size_t v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_usize_dec_lt(v_i_1189_, v_sz_1188_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_goal_1185_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_b_1190_);
return v___x_1197_;
}
else
{
lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1239_; 
v_snd_1198_ = lean_ctor_get(v_b_1190_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_b_1190_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_b_1190_, 0);
lean_dec(v_unused_1240_);
v___x_1200_ = v_b_1190_;
v_isShared_1201_ = v_isSharedCheck_1239_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_dec(v_b_1190_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1239_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1202_ = lean_array_uget_borrowed(v_as_1187_, v_i_1189_);
lean_inc(v_a_1202_);
lean_inc_ref(v_goal_1185_);
v___x_1203_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1185_, v_a_1202_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v_a_1207_; uint8_t v___x_1214_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = lean_box(0);
v___x_1214_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1204_);
if (v___x_1214_ == 0)
{
lean_dec(v_a_1204_);
v_a_1207_ = v_snd_1198_;
goto v___jp_1206_;
}
else
{
lean_object* v_type_1215_; lean_object* v___x_1216_; 
v_type_1215_ = lean_ctor_get(v___x_1186_, 2);
lean_inc(v_a_1204_);
lean_inc_ref(v_type_1215_);
v___x_1216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1215_, v_a_1204_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; uint8_t v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
if (v___x_1218_ == 0)
{
lean_dec(v_a_1204_);
v_a_1207_ = v_snd_1198_;
goto v___jp_1206_;
}
else
{
lean_object* v_self_1219_; lean_object* v___x_1220_; 
v_self_1219_ = lean_ctor_get(v_a_1204_, 0);
lean_inc_ref(v_self_1219_);
lean_dec(v_a_1204_);
lean_inc_ref(v___x_1186_);
v___x_1220_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1186_, v_self_1219_);
if (lean_obj_tag(v___x_1220_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1222_; 
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1221_);
lean_dec_ref(v___x_1220_);
lean_inc_ref(v_goal_1185_);
v___x_1222_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1185_, v_self_1219_, v_val_1221_, v_snd_1198_);
v_a_1207_ = v___x_1222_;
goto v___jp_1206_;
}
else
{
lean_dec(v___x_1220_);
lean_dec_ref(v_self_1219_);
v_a_1207_ = v_snd_1198_;
goto v___jp_1206_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1204_);
lean_del_object(v___x_1200_);
lean_dec(v_snd_1198_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_goal_1185_);
v_a_1223_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1216_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1216_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_a_1207_);
lean_ctor_set(v___x_1200_, 0, v___x_1205_);
v___x_1209_ = v___x_1200_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_a_1207_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
size_t v___x_1210_; size_t v___x_1211_; 
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_i_1189_, v___x_1210_);
v_i_1189_ = v___x_1211_;
v_b_1190_ = v___x_1209_;
goto _start;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_del_object(v___x_1200_);
lean_dec(v_snd_1198_);
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_goal_1185_);
v_a_1231_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1203_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1203_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1241_, lean_object* v___x_1242_, lean_object* v_as_1243_, lean_object* v_sz_1244_, lean_object* v_i_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
size_t v_sz_boxed_1252_; size_t v_i_boxed_1253_; lean_object* v_res_1254_; 
v_sz_boxed_1252_ = lean_unbox_usize(v_sz_1244_);
lean_dec(v_sz_1244_);
v_i_boxed_1253_ = lean_unbox_usize(v_i_1245_);
lean_dec(v_i_1245_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1241_, v___x_1242_, v_as_1243_, v_sz_boxed_1252_, v_i_boxed_1253_, v_b_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_as_1243_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1255_, lean_object* v___x_1256_, lean_object* v_as_1257_, size_t v_sz_1258_, size_t v_i_1259_, lean_object* v_b_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1259_, v_sz_1258_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v___x_1256_);
lean_dec_ref(v_goal_1255_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1260_);
return v___x_1267_;
}
else
{
lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1309_; 
v_snd_1268_ = lean_ctor_get(v_b_1260_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_b_1260_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_b_1260_, 0);
lean_dec(v_unused_1310_);
v___x_1270_ = v_b_1260_;
v_isShared_1271_ = v_isSharedCheck_1309_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_dec(v_b_1260_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1309_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_array_uget_borrowed(v_as_1257_, v_i_1259_);
lean_inc(v_a_1272_);
lean_inc_ref(v_goal_1255_);
v___x_1273_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1255_, v_a_1272_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v_a_1277_; uint8_t v___x_1284_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
v___x_1275_ = lean_box(0);
v___x_1284_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1274_);
if (v___x_1284_ == 0)
{
lean_dec(v_a_1274_);
v_a_1277_ = v_snd_1268_;
goto v___jp_1276_;
}
else
{
lean_object* v_type_1285_; lean_object* v___x_1286_; 
v_type_1285_ = lean_ctor_get(v___x_1256_, 2);
lean_inc(v_a_1274_);
lean_inc_ref(v_type_1285_);
v___x_1286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1285_, v_a_1274_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
lean_dec(v_a_1274_);
v_a_1277_ = v_snd_1268_;
goto v___jp_1276_;
}
else
{
lean_object* v_self_1289_; lean_object* v___x_1290_; 
v_self_1289_ = lean_ctor_get(v_a_1274_, 0);
lean_inc_ref(v_self_1289_);
lean_dec(v_a_1274_);
lean_inc_ref(v___x_1256_);
v___x_1290_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1256_, v_self_1289_);
if (lean_obj_tag(v___x_1290_) == 1)
{
lean_object* v_val_1291_; lean_object* v___x_1292_; 
v_val_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1291_);
lean_dec_ref(v___x_1290_);
lean_inc_ref(v_goal_1255_);
v___x_1292_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1255_, v_self_1289_, v_val_1291_, v_snd_1268_);
v_a_1277_ = v___x_1292_;
goto v___jp_1276_;
}
else
{
lean_dec(v___x_1290_);
lean_dec_ref(v_self_1289_);
v_a_1277_ = v_snd_1268_;
goto v___jp_1276_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1274_);
lean_del_object(v___x_1270_);
lean_dec(v_snd_1268_);
lean_dec_ref(v___x_1256_);
lean_dec_ref(v_goal_1255_);
v_a_1293_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1286_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1286_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
v___jp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_a_1277_);
lean_ctor_set(v___x_1270_, 0, v___x_1275_);
v___x_1279_ = v___x_1270_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1259_, v___x_1280_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1255_, v___x_1256_, v_as_1257_, v_sz_1258_, v___x_1281_, v___x_1279_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_del_object(v___x_1270_);
lean_dec(v_snd_1268_);
lean_dec_ref(v___x_1256_);
lean_dec_ref(v_goal_1255_);
v_a_1301_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1273_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1273_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1311_, lean_object* v___x_1312_, lean_object* v_as_1313_, lean_object* v_sz_1314_, lean_object* v_i_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
size_t v_sz_boxed_1322_; size_t v_i_boxed_1323_; lean_object* v_res_1324_; 
v_sz_boxed_1322_ = lean_unbox_usize(v_sz_1314_);
lean_dec(v_sz_1314_);
v_i_boxed_1323_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_res_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1311_, v___x_1312_, v_as_1313_, v_sz_boxed_1322_, v_i_boxed_1323_, v_b_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v_as_1313_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1325_, lean_object* v_goal_1326_, lean_object* v___x_1327_, lean_object* v_n_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
if (lean_obj_tag(v_n_1328_) == 0)
{
lean_object* v_cs_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1369_; 
v_cs_1335_ = lean_ctor_get(v_n_1328_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_n_1328_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1337_ = v_n_1328_;
v_isShared_1338_ = v_isSharedCheck_1369_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_cs_1335_);
lean_dec(v_n_1328_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1369_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; size_t v_sz_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_b_1329_);
v_sz_1341_ = lean_array_size(v_cs_1335_);
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1325_, v_goal_1326_, v___x_1327_, v_cs_1335_, v_sz_1341_, v___x_1342_, v___x_1340_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec_ref(v_cs_1335_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1360_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1360_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1360_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_fst_1348_; 
v_fst_1348_ = lean_ctor_get(v_a_1344_, 0);
if (lean_obj_tag(v_fst_1348_) == 0)
{
lean_object* v_snd_1349_; lean_object* v___x_1351_; 
v_snd_1349_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1349_);
lean_dec(v_a_1344_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
lean_ctor_set(v___x_1337_, 0, v_snd_1349_);
v___x_1351_ = v___x_1337_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_snd_1349_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1351_);
v___x_1353_ = v___x_1346_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1358_; 
lean_inc_ref(v_fst_1348_);
lean_dec(v_a_1344_);
lean_del_object(v___x_1337_);
v_val_1356_ = lean_ctor_get(v_fst_1348_, 0);
lean_inc(v_val_1356_);
lean_dec_ref(v_fst_1348_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_val_1356_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_del_object(v___x_1337_);
v_a_1361_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1343_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1343_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
}
else
{
lean_object* v_vs_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1404_; 
v_vs_1370_ = lean_ctor_get(v_n_1328_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_n_1328_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1372_ = v_n_1328_;
v_isShared_1373_ = v_isSharedCheck_1404_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_vs_1370_);
lean_dec(v_n_1328_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1404_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v_b_1329_);
v_sz_1376_ = lean_array_size(v_vs_1370_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1326_, v___x_1327_, v_vs_1370_, v_sz_1376_, v___x_1377_, v___x_1375_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec_ref(v_vs_1370_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1395_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1395_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1395_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_fst_1383_; 
v_fst_1383_ = lean_ctor_get(v_a_1379_, 0);
if (lean_obj_tag(v_fst_1383_) == 0)
{
lean_object* v_snd_1384_; lean_object* v___x_1386_; 
v_snd_1384_ = lean_ctor_get(v_a_1379_, 1);
lean_inc(v_snd_1384_);
lean_dec(v_a_1379_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_snd_1384_);
v___x_1386_ = v___x_1372_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_snd_1384_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1386_);
v___x_1388_ = v___x_1381_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1393_; 
lean_inc_ref(v_fst_1383_);
lean_dec(v_a_1379_);
lean_del_object(v___x_1372_);
v_val_1391_ = lean_ctor_get(v_fst_1383_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v_fst_1383_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_val_1391_);
v___x_1393_ = v___x_1381_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_val_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1372_);
v_a_1396_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1378_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1378_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1405_, lean_object* v_goal_1406_, lean_object* v___x_1407_, lean_object* v_as_1408_, size_t v_sz_1409_, size_t v_i_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_lt(v_i_1410_, v_sz_1409_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v___x_1407_);
lean_dec_ref(v_goal_1406_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_b_1411_);
return v___x_1418_;
}
else
{
lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1453_; 
v_snd_1419_ = lean_ctor_get(v_b_1411_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_b_1411_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_b_1411_, 0);
lean_dec(v_unused_1454_);
v___x_1421_ = v_b_1411_;
v_isShared_1422_ = v_isSharedCheck_1453_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_dec(v_b_1411_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1453_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_array_uget_borrowed(v_as_1408_, v_i_1410_);
lean_inc(v_snd_1419_);
lean_inc(v_a_1423_);
lean_inc_ref(v___x_1407_);
lean_inc_ref(v_goal_1406_);
v___x_1424_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1405_, v_goal_1406_, v___x_1407_, v_a_1423_, v_snd_1419_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1444_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1444_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1444_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
if (lean_obj_tag(v_a_1425_) == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec_ref(v___x_1407_);
lean_dec_ref(v_goal_1406_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_a_1425_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1429_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_snd_1419_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1431_);
v___x_1433_ = v___x_1427_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_del_object(v___x_1427_);
lean_dec(v_snd_1419_);
v_a_1436_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_a_1436_);
lean_dec_ref(v_a_1425_);
v___x_1437_ = lean_box(0);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_a_1436_);
lean_ctor_set(v___x_1421_, 0, v___x_1437_);
v___x_1439_ = v___x_1421_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1436_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
size_t v___x_1440_; size_t v___x_1441_; 
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_i_1410_, v___x_1440_);
v_i_1410_ = v___x_1441_;
v_b_1411_ = v___x_1439_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_del_object(v___x_1421_);
lean_dec(v_snd_1419_);
lean_dec_ref(v___x_1407_);
lean_dec_ref(v_goal_1406_);
v_a_1445_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1424_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1424_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1455_, lean_object* v_goal_1456_, lean_object* v___x_1457_, lean_object* v_as_1458_, lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
size_t v_sz_boxed_1467_; size_t v_i_boxed_1468_; lean_object* v_res_1469_; 
v_sz_boxed_1467_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1468_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1455_, v_goal_1456_, v___x_1457_, v_as_1458_, v_sz_boxed_1467_, v_i_boxed_1468_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v_as_1458_);
lean_dec_ref(v_init_1455_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1470_, lean_object* v_goal_1471_, lean_object* v___x_1472_, lean_object* v_n_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1470_, v_goal_1471_, v___x_1472_, v_n_1473_, v_b_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v_init_1470_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1481_, lean_object* v___x_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v___x_1482_);
lean_dec_ref(v_goal_1481_);
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
lean_inc_ref(v_goal_1481_);
v___x_1499_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1481_, v_a_1498_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v_a_1503_; uint8_t v___x_1510_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
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
lean_dec_ref(v___x_1512_);
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
lean_inc_ref(v___x_1482_);
v___x_1516_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1482_, v_self_1515_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref(v___x_1516_);
lean_inc_ref(v_goal_1481_);
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
lean_dec_ref(v_goal_1481_);
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
size_t v___x_1506_; size_t v___x_1507_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1485_, v___x_1506_);
v_i_1485_ = v___x_1507_;
v_b_1486_ = v___x_1505_;
goto _start;
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
lean_dec_ref(v___x_1482_);
lean_dec_ref(v_goal_1481_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1537_, lean_object* v___x_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1537_, v___x_1538_, v_as_1539_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_as_1539_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1551_, lean_object* v___x_1552_, lean_object* v_as_1553_, size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_goal_1551_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_b_1556_);
return v___x_1563_;
}
else
{
lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1605_; 
v_snd_1564_ = lean_ctor_get(v_b_1556_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_b_1556_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_b_1556_, 0);
lean_dec(v_unused_1606_);
v___x_1566_ = v_b_1556_;
v_isShared_1567_ = v_isSharedCheck_1605_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_dec(v_b_1556_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1605_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_array_uget_borrowed(v_as_1553_, v_i_1555_);
lean_inc(v_a_1568_);
lean_inc_ref(v_goal_1551_);
v___x_1569_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1551_, v_a_1568_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v_a_1573_; uint8_t v___x_1580_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = lean_box(0);
v___x_1580_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1570_);
if (v___x_1580_ == 0)
{
lean_dec(v_a_1570_);
v_a_1573_ = v_snd_1564_;
goto v___jp_1572_;
}
else
{
lean_object* v_type_1581_; lean_object* v___x_1582_; 
v_type_1581_ = lean_ctor_get(v___x_1552_, 2);
lean_inc(v_a_1570_);
lean_inc_ref(v_type_1581_);
v___x_1582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1581_, v_a_1570_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; uint8_t v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = lean_unbox(v_a_1583_);
lean_dec(v_a_1583_);
if (v___x_1584_ == 0)
{
lean_dec(v_a_1570_);
v_a_1573_ = v_snd_1564_;
goto v___jp_1572_;
}
else
{
lean_object* v_self_1585_; lean_object* v___x_1586_; 
v_self_1585_ = lean_ctor_get(v_a_1570_, 0);
lean_inc_ref(v_self_1585_);
lean_dec(v_a_1570_);
lean_inc_ref(v___x_1552_);
v___x_1586_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1552_, v_self_1585_);
if (lean_obj_tag(v___x_1586_) == 1)
{
lean_object* v_val_1587_; lean_object* v___x_1588_; 
v_val_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref(v___x_1586_);
lean_inc_ref(v_goal_1551_);
v___x_1588_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1551_, v_self_1585_, v_val_1587_, v_snd_1564_);
v_a_1573_ = v___x_1588_;
goto v___jp_1572_;
}
else
{
lean_dec(v___x_1586_);
lean_dec_ref(v_self_1585_);
v_a_1573_ = v_snd_1564_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_a_1570_);
lean_del_object(v___x_1566_);
lean_dec(v_snd_1564_);
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_goal_1551_);
v_a_1589_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1582_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1582_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
v___jp_1572_:
{
lean_object* v___x_1575_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_a_1573_);
lean_ctor_set(v___x_1566_, 0, v___x_1571_);
v___x_1575_ = v___x_1566_;
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
v___x_1577_ = lean_usize_add(v_i_1555_, v___x_1576_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1551_, v___x_1552_, v_as_1553_, v_sz_1554_, v___x_1577_, v___x_1575_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1566_);
lean_dec(v_snd_1564_);
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_goal_1551_);
v_a_1597_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1569_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1569_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1607_, lean_object* v___x_1608_, lean_object* v_as_1609_, lean_object* v_sz_1610_, lean_object* v_i_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_sz_boxed_1618_; size_t v_i_boxed_1619_; lean_object* v_res_1620_; 
v_sz_boxed_1618_ = lean_unbox_usize(v_sz_1610_);
lean_dec(v_sz_1610_);
v_i_boxed_1619_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1607_, v___x_1608_, v_as_1609_, v_sz_boxed_1618_, v_i_boxed_1619_, v_b_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_as_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1621_, lean_object* v___x_1622_, lean_object* v_t_1623_, lean_object* v_init_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_root_1630_; lean_object* v_tail_1631_; lean_object* v___x_1632_; 
v_root_1630_ = lean_ctor_get(v_t_1623_, 0);
lean_inc_ref(v_root_1630_);
v_tail_1631_ = lean_ctor_get(v_t_1623_, 1);
lean_inc_ref(v_tail_1631_);
lean_dec_ref(v_t_1623_);
lean_inc_ref(v___x_1622_);
lean_inc_ref(v_goal_1621_);
lean_inc_ref(v_init_1624_);
v___x_1632_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1624_, v_goal_1621_, v___x_1622_, v_root_1630_, v_init_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_init_1624_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1669_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1669_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1669_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
if (lean_obj_tag(v_a_1633_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; 
lean_dec_ref(v_tail_1631_);
lean_dec_ref(v___x_1622_);
lean_dec_ref(v_goal_1621_);
v_a_1637_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_a_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; size_t v_sz_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1635_);
v_a_1641_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v_a_1633_);
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1641_);
v_sz_1644_ = lean_array_size(v_tail_1631_);
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1621_, v___x_1622_, v_tail_1631_, v_sz_1644_, v___x_1645_, v___x_1643_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_tail_1631_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1660_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
if (lean_obj_tag(v_fst_1651_) == 0)
{
lean_object* v_snd_1652_; lean_object* v___x_1654_; 
v_snd_1652_ = lean_ctor_get(v_a_1647_, 1);
lean_inc(v_snd_1652_);
lean_dec(v_a_1647_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_snd_1652_);
v___x_1654_ = v___x_1649_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_snd_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1658_; 
lean_inc_ref(v_fst_1651_);
lean_dec(v_a_1647_);
v_val_1656_ = lean_ctor_get(v_fst_1651_, 0);
lean_inc(v_val_1656_);
lean_dec_ref(v_fst_1651_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_val_1656_);
v___x_1658_ = v___x_1649_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_val_1656_);
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
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1646_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1646_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_tail_1631_);
lean_dec_ref(v___x_1622_);
lean_dec_ref(v_goal_1621_);
v_a_1670_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1632_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1632_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1678_, lean_object* v___x_1679_, lean_object* v_t_1680_, lean_object* v_init_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1678_, v___x_1679_, v_t_1680_, v_init_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1688_, lean_object* v_as_1689_, size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_lt(v_i_1691_, v_sz_1690_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_dec_ref(v_goal_1688_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_b_1692_);
return v___x_1699_;
}
else
{
lean_object* v_snd_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1731_; 
v_snd_1700_ = lean_ctor_get(v_b_1692_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_b_1692_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v_b_1692_, 0);
lean_dec(v_unused_1732_);
v___x_1702_ = v_b_1692_;
v_isShared_1703_ = v_isSharedCheck_1731_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snd_1700_);
lean_dec(v_b_1692_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1731_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_array_uget_borrowed(v_as_1689_, v_i_1691_);
lean_inc(v_a_1704_);
lean_inc_ref(v_goal_1688_);
v___x_1705_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1688_, v_a_1704_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v_self_1707_; lean_object* v___x_1708_; lean_object* v_a_1710_; lean_object* v___x_1717_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v_self_1707_ = lean_ctor_get(v_a_1706_, 0);
lean_inc_ref_n(v_self_1707_, 2);
lean_dec(v_a_1706_);
v___x_1708_ = lean_box(0);
v___x_1717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1707_);
if (lean_obj_tag(v___x_1717_) == 1)
{
lean_object* v_val_1718_; lean_object* v___x_1719_; 
v_val_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1700_, v_val_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1700_, v_self_1707_);
lean_dec_ref(v_self_1707_);
if (lean_obj_tag(v___x_1720_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1722_; 
v_val_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v___x_1720_);
lean_inc_ref(v_goal_1688_);
v___x_1722_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1688_, v_val_1718_, v_val_1721_, v_snd_1700_);
v_a_1710_ = v___x_1722_;
goto v___jp_1709_;
}
else
{
lean_dec(v___x_1720_);
lean_dec(v_val_1718_);
v_a_1710_ = v_snd_1700_;
goto v___jp_1709_;
}
}
else
{
lean_dec_ref(v___x_1719_);
lean_dec(v_val_1718_);
lean_dec_ref(v_self_1707_);
v_a_1710_ = v_snd_1700_;
goto v___jp_1709_;
}
}
else
{
lean_dec(v___x_1717_);
lean_dec_ref(v_self_1707_);
v_a_1710_ = v_snd_1700_;
goto v___jp_1709_;
}
v___jp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_a_1710_);
lean_ctor_set(v___x_1702_, 0, v___x_1708_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1710_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
size_t v___x_1713_; size_t v___x_1714_; 
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1691_, v___x_1713_);
v_i_1691_ = v___x_1714_;
v_b_1692_ = v___x_1712_;
goto _start;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_del_object(v___x_1702_);
lean_dec(v_snd_1700_);
lean_dec_ref(v_goal_1688_);
v_a_1723_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1705_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1705_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1733_, lean_object* v_as_1734_, lean_object* v_sz_1735_, lean_object* v_i_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
size_t v_sz_boxed_1743_; size_t v_i_boxed_1744_; lean_object* v_res_1745_; 
v_sz_boxed_1743_ = lean_unbox_usize(v_sz_1735_);
lean_dec(v_sz_1735_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1733_, v_as_1734_, v_sz_boxed_1743_, v_i_boxed_1744_, v_b_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_as_1734_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1746_, lean_object* v_as_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_goal_1746_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_b_1750_);
return v___x_1757_;
}
else
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1789_; 
v_snd_1758_ = lean_ctor_get(v_b_1750_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_b_1750_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_b_1750_, 0);
lean_dec(v_unused_1790_);
v___x_1760_ = v_b_1750_;
v_isShared_1761_ = v_isSharedCheck_1789_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snd_1758_);
lean_dec(v_b_1750_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1789_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_array_uget_borrowed(v_as_1747_, v_i_1749_);
lean_inc(v_a_1762_);
lean_inc_ref(v_goal_1746_);
v___x_1763_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1746_, v_a_1762_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_self_1765_; lean_object* v___x_1766_; lean_object* v_a_1768_; lean_object* v___x_1775_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v_self_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc_ref_n(v_self_1765_, 2);
lean_dec(v_a_1764_);
v___x_1766_ = lean_box(0);
v___x_1775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1765_);
if (lean_obj_tag(v___x_1775_) == 1)
{
lean_object* v_val_1776_; lean_object* v___x_1777_; 
v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1758_, v_val_1776_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1758_, v_self_1765_);
lean_dec_ref(v_self_1765_);
if (lean_obj_tag(v___x_1778_) == 1)
{
lean_object* v_val_1779_; lean_object* v___x_1780_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref(v___x_1778_);
lean_inc_ref(v_goal_1746_);
v___x_1780_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1746_, v_val_1776_, v_val_1779_, v_snd_1758_);
v_a_1768_ = v___x_1780_;
goto v___jp_1767_;
}
else
{
lean_dec(v___x_1778_);
lean_dec(v_val_1776_);
v_a_1768_ = v_snd_1758_;
goto v___jp_1767_;
}
}
else
{
lean_dec_ref(v___x_1777_);
lean_dec(v_val_1776_);
lean_dec_ref(v_self_1765_);
v_a_1768_ = v_snd_1758_;
goto v___jp_1767_;
}
}
else
{
lean_dec(v___x_1775_);
lean_dec_ref(v_self_1765_);
v_a_1768_ = v_snd_1758_;
goto v___jp_1767_;
}
v___jp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v_a_1768_);
lean_ctor_set(v___x_1760_, 0, v___x_1766_);
v___x_1770_ = v___x_1760_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1768_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1749_, v___x_1771_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1746_, v_as_1747_, v_sz_1748_, v___x_1772_, v___x_1770_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1760_);
lean_dec(v_snd_1758_);
lean_dec_ref(v_goal_1746_);
v_a_1781_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1763_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1763_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1791_, lean_object* v_as_1792_, lean_object* v_sz_1793_, lean_object* v_i_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
size_t v_sz_boxed_1801_; size_t v_i_boxed_1802_; lean_object* v_res_1803_; 
v_sz_boxed_1801_ = lean_unbox_usize(v_sz_1793_);
lean_dec(v_sz_1793_);
v_i_boxed_1802_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_res_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1791_, v_as_1792_, v_sz_boxed_1801_, v_i_boxed_1802_, v_b_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_as_1792_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1804_, lean_object* v_as_1805_, size_t v_sz_1806_, size_t v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_lt(v_i_1807_, v_sz_1806_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec_ref(v_goal_1804_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_b_1808_);
return v___x_1815_;
}
else
{
lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1847_; 
v_snd_1816_ = lean_ctor_get(v_b_1808_, 1);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_b_1808_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_b_1808_, 0);
lean_dec(v_unused_1848_);
v___x_1818_ = v_b_1808_;
v_isShared_1819_ = v_isSharedCheck_1847_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_dec(v_b_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1847_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_array_uget_borrowed(v_as_1805_, v_i_1807_);
lean_inc(v_a_1820_);
lean_inc_ref(v_goal_1804_);
v___x_1821_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1804_, v_a_1820_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v_self_1823_; lean_object* v___x_1824_; lean_object* v_a_1826_; lean_object* v___x_1833_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v_self_1823_ = lean_ctor_get(v_a_1822_, 0);
lean_inc_ref_n(v_self_1823_, 2);
lean_dec(v_a_1822_);
v___x_1824_ = lean_box(0);
v___x_1833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1823_);
if (lean_obj_tag(v___x_1833_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1835_; 
v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1816_, v_val_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1816_, v_self_1823_);
lean_dec_ref(v_self_1823_);
if (lean_obj_tag(v___x_1836_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; 
v_val_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1837_);
lean_dec_ref(v___x_1836_);
lean_inc_ref(v_goal_1804_);
v___x_1838_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1804_, v_val_1834_, v_val_1837_, v_snd_1816_);
v_a_1826_ = v___x_1838_;
goto v___jp_1825_;
}
else
{
lean_dec(v___x_1836_);
lean_dec(v_val_1834_);
v_a_1826_ = v_snd_1816_;
goto v___jp_1825_;
}
}
else
{
lean_dec_ref(v___x_1835_);
lean_dec(v_val_1834_);
lean_dec_ref(v_self_1823_);
v_a_1826_ = v_snd_1816_;
goto v___jp_1825_;
}
}
else
{
lean_dec(v___x_1833_);
lean_dec_ref(v_self_1823_);
v_a_1826_ = v_snd_1816_;
goto v___jp_1825_;
}
v___jp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v_a_1826_);
lean_ctor_set(v___x_1818_, 0, v___x_1824_);
v___x_1828_ = v___x_1818_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_a_1826_);
v___x_1828_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
size_t v___x_1829_; size_t v___x_1830_; 
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1807_, v___x_1829_);
v_i_1807_ = v___x_1830_;
v_b_1808_ = v___x_1828_;
goto _start;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec_ref(v_goal_1804_);
v_a_1839_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1821_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1821_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1849_, lean_object* v_as_1850_, lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
size_t v_sz_boxed_1859_; size_t v_i_boxed_1860_; lean_object* v_res_1861_; 
v_sz_boxed_1859_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1860_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1849_, v_as_1850_, v_sz_boxed_1859_, v_i_boxed_1860_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v_as_1850_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1862_, lean_object* v_as_1863_, size_t v_sz_1864_, size_t v_i_1865_, lean_object* v_b_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_usize_dec_lt(v_i_1865_, v_sz_1864_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v_goal_1862_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_b_1866_);
return v___x_1873_;
}
else
{
lean_object* v_snd_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1905_; 
v_snd_1874_ = lean_ctor_get(v_b_1866_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_b_1866_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v_b_1866_, 0);
lean_dec(v_unused_1906_);
v___x_1876_ = v_b_1866_;
v_isShared_1877_ = v_isSharedCheck_1905_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snd_1874_);
lean_dec(v_b_1866_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1905_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_array_uget_borrowed(v_as_1863_, v_i_1865_);
lean_inc(v_a_1878_);
lean_inc_ref(v_goal_1862_);
v___x_1879_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1862_, v_a_1878_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v_self_1881_; lean_object* v___x_1882_; lean_object* v_a_1884_; lean_object* v___x_1891_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v_self_1881_ = lean_ctor_get(v_a_1880_, 0);
lean_inc_ref_n(v_self_1881_, 2);
lean_dec(v_a_1880_);
v___x_1882_ = lean_box(0);
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1881_);
if (lean_obj_tag(v___x_1891_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1893_; 
v_val_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1892_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1874_, v_val_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1874_, v_self_1881_);
lean_dec_ref(v_self_1881_);
if (lean_obj_tag(v___x_1894_) == 1)
{
lean_object* v_val_1895_; lean_object* v___x_1896_; 
v_val_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_val_1895_);
lean_dec_ref(v___x_1894_);
lean_inc_ref(v_goal_1862_);
v___x_1896_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1862_, v_val_1892_, v_val_1895_, v_snd_1874_);
v_a_1884_ = v___x_1896_;
goto v___jp_1883_;
}
else
{
lean_dec(v___x_1894_);
lean_dec(v_val_1892_);
v_a_1884_ = v_snd_1874_;
goto v___jp_1883_;
}
}
else
{
lean_dec_ref(v___x_1893_);
lean_dec(v_val_1892_);
lean_dec_ref(v_self_1881_);
v_a_1884_ = v_snd_1874_;
goto v___jp_1883_;
}
}
else
{
lean_dec(v___x_1891_);
lean_dec_ref(v_self_1881_);
v_a_1884_ = v_snd_1874_;
goto v___jp_1883_;
}
v___jp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_a_1884_);
lean_ctor_set(v___x_1876_, 0, v___x_1882_);
v___x_1886_ = v___x_1876_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_a_1884_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1865_, v___x_1887_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1862_, v_as_1863_, v_sz_1864_, v___x_1888_, v___x_1886_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1889_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_del_object(v___x_1876_);
lean_dec(v_snd_1874_);
lean_dec_ref(v_goal_1862_);
v_a_1897_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1879_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1879_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1907_, lean_object* v_as_1908_, lean_object* v_sz_1909_, lean_object* v_i_1910_, lean_object* v_b_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1909_);
lean_dec(v_sz_1909_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1910_);
lean_dec(v_i_1910_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1907_, v_as_1908_, v_sz_boxed_1917_, v_i_boxed_1918_, v_b_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v_as_1908_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1920_, lean_object* v_goal_1921_, lean_object* v_n_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
if (lean_obj_tag(v_n_1922_) == 0)
{
lean_object* v_cs_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1963_; 
v_cs_1929_ = lean_ctor_get(v_n_1922_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_n_1922_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1931_ = v_n_1922_;
v_isShared_1932_ = v_isSharedCheck_1963_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_cs_1929_);
lean_dec(v_n_1922_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1963_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; size_t v_sz_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v_b_1923_);
v_sz_1935_ = lean_array_size(v_cs_1929_);
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1920_, v_goal_1921_, v_cs_1929_, v_sz_1935_, v___x_1936_, v___x_1934_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec_ref(v_cs_1929_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1954_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_fst_1942_; 
v_fst_1942_ = lean_ctor_get(v_a_1938_, 0);
if (lean_obj_tag(v_fst_1942_) == 0)
{
lean_object* v_snd_1943_; lean_object* v___x_1945_; 
v_snd_1943_ = lean_ctor_get(v_a_1938_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_a_1938_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 0, v_snd_1943_);
v___x_1945_ = v___x_1931_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_snd_1943_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1945_);
v___x_1947_ = v___x_1940_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_object* v_val_1950_; lean_object* v___x_1952_; 
lean_inc_ref(v_fst_1942_);
lean_dec(v_a_1938_);
lean_del_object(v___x_1931_);
v_val_1950_ = lean_ctor_get(v_fst_1942_, 0);
lean_inc(v_val_1950_);
lean_dec_ref(v_fst_1942_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v_val_1950_);
v___x_1952_ = v___x_1940_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_val_1950_);
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
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1931_);
v_a_1955_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1937_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1937_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
else
{
lean_object* v_vs_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1998_; 
v_vs_1964_ = lean_ctor_get(v_n_1922_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_n_1922_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1966_ = v_n_1922_;
v_isShared_1967_ = v_isSharedCheck_1998_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_vs_1964_);
lean_dec(v_n_1922_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1998_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; size_t v_sz_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v_b_1923_);
v_sz_1970_ = lean_array_size(v_vs_1964_);
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1921_, v_vs_1964_, v_sz_1970_, v___x_1971_, v___x_1969_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec_ref(v_vs_1964_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1989_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1989_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1989_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_fst_1977_; 
v_fst_1977_ = lean_ctor_get(v_a_1973_, 0);
if (lean_obj_tag(v_fst_1977_) == 0)
{
lean_object* v_snd_1978_; lean_object* v___x_1980_; 
v_snd_1978_ = lean_ctor_get(v_a_1973_, 1);
lean_inc(v_snd_1978_);
lean_dec(v_a_1973_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_snd_1978_);
v___x_1980_ = v___x_1966_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_snd_1978_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1980_);
v___x_1982_ = v___x_1975_;
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
lean_object* v_val_1985_; lean_object* v___x_1987_; 
lean_inc_ref(v_fst_1977_);
lean_dec(v_a_1973_);
lean_del_object(v___x_1966_);
v_val_1985_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_val_1985_);
lean_dec_ref(v_fst_1977_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_val_1985_);
v___x_1987_ = v___x_1975_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_val_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_del_object(v___x_1966_);
v_a_1990_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1972_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1972_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1999_, lean_object* v_goal_2000_, lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v_goal_2000_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_b_2004_);
return v___x_2011_;
}
else
{
lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2046_; 
v_snd_2012_ = lean_ctor_get(v_b_2004_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_b_2004_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_b_2004_, 0);
lean_dec(v_unused_2047_);
v___x_2014_ = v_b_2004_;
v_isShared_2015_ = v_isSharedCheck_2046_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_dec(v_b_2004_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2046_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_array_uget_borrowed(v_as_2001_, v_i_2003_);
lean_inc(v_snd_2012_);
lean_inc(v_a_2016_);
lean_inc_ref(v_goal_2000_);
v___x_2017_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1999_, v_goal_2000_, v_a_2016_, v_snd_2012_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2037_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2037_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
if (lean_obj_tag(v_a_2018_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_dec_ref(v_goal_2000_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_a_2018_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2022_);
v___x_2024_ = v___x_2014_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_snd_2012_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2024_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_del_object(v___x_2020_);
lean_dec(v_snd_2012_);
v_a_2029_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v_a_2018_);
v___x_2030_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v_a_2029_);
lean_ctor_set(v___x_2014_, 0, v___x_2030_);
v___x_2032_ = v___x_2014_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_a_2029_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2003_, v___x_2033_);
v_i_2003_ = v___x_2034_;
v_b_2004_ = v___x_2032_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_2014_);
lean_dec(v_snd_2012_);
lean_dec_ref(v_goal_2000_);
v_a_2038_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2017_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2017_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2048_, lean_object* v_goal_2049_, lean_object* v_as_2050_, lean_object* v_sz_2051_, lean_object* v_i_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_sz_boxed_2059_; size_t v_i_boxed_2060_; lean_object* v_res_2061_; 
v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2051_);
lean_dec(v_sz_2051_);
v_i_boxed_2060_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2048_, v_goal_2049_, v_as_2050_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_as_2050_);
lean_dec_ref(v_init_2048_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2062_, lean_object* v_goal_2063_, lean_object* v_n_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2062_, v_goal_2063_, v_n_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec_ref(v_init_2062_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2072_, lean_object* v_t_2073_, lean_object* v_init_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_root_2080_; lean_object* v_tail_2081_; lean_object* v___x_2082_; 
v_root_2080_ = lean_ctor_get(v_t_2073_, 0);
lean_inc_ref(v_root_2080_);
v_tail_2081_ = lean_ctor_get(v_t_2073_, 1);
lean_inc_ref(v_tail_2081_);
lean_dec_ref(v_t_2073_);
lean_inc_ref(v_goal_2072_);
lean_inc_ref(v_init_2074_);
v___x_2082_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2074_, v_goal_2072_, v_root_2080_, v_init_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec_ref(v_init_2074_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2119_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2119_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2119_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
if (lean_obj_tag(v_a_2083_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; 
lean_dec_ref(v_tail_2081_);
lean_dec_ref(v_goal_2072_);
v_a_2087_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v_a_2083_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_a_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; size_t v_sz_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_2085_);
v_a_2091_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v_a_2083_);
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_a_2091_);
v_sz_2094_ = lean_array_size(v_tail_2081_);
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2072_, v_tail_2081_, v_sz_2094_, v___x_2095_, v___x_2093_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec_ref(v_tail_2081_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2110_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_fst_2101_; 
v_fst_2101_ = lean_ctor_get(v_a_2097_, 0);
if (lean_obj_tag(v_fst_2101_) == 0)
{
lean_object* v_snd_2102_; lean_object* v___x_2104_; 
v_snd_2102_ = lean_ctor_get(v_a_2097_, 1);
lean_inc(v_snd_2102_);
lean_dec(v_a_2097_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v_snd_2102_);
v___x_2104_ = v___x_2099_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_snd_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v_val_2106_; lean_object* v___x_2108_; 
lean_inc_ref(v_fst_2101_);
lean_dec(v_a_2097_);
v_val_2106_ = lean_ctor_get(v_fst_2101_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v_fst_2101_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v_val_2106_);
v___x_2108_ = v___x_2099_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2096_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2096_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_tail_2081_);
lean_dec_ref(v_goal_2072_);
v_a_2120_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2082_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2082_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2150_, lean_object* v_structId_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2158_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2157_, v_goal_2150_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_toGoalState_2160_; lean_object* v_structs_2161_; lean_object* v_exprs_2162_; lean_object* v___x_2163_; lean_object* v_model_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
v_toGoalState_2160_ = lean_ctor_get(v_goal_2150_, 0);
v_structs_2161_ = lean_ctor_get(v_a_2159_, 0);
lean_inc_ref(v_structs_2161_);
lean_dec(v_a_2159_);
v_exprs_2162_ = lean_ctor_get(v_toGoalState_2160_, 2);
v___x_2163_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2164_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2165_ = lean_array_get(v___x_2163_, v_structs_2161_, v_structId_2151_);
lean_dec_ref(v_structs_2161_);
lean_inc_ref(v_exprs_2162_);
lean_inc(v___x_2165_);
lean_inc_ref(v_goal_2150_);
v___x_2166_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2150_, v___x_2165_, v_exprs_2162_, v_model_2164_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2166_);
lean_inc_ref(v_goal_2150_);
v___x_2168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2150_, v_structId_2151_, v_a_2167_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
lean_inc_ref(v_exprs_2162_);
lean_inc_ref(v_goal_2150_);
v___x_2170_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2150_, v_exprs_2162_, v_a_2169_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_type_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v_type_2172_ = lean_ctor_get(v___x_2165_, 2);
lean_inc_ref(v_type_2172_);
lean_dec(v___x_2165_);
v___x_2173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2173_, 0, v_type_2172_);
v___x_2174_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2150_, v___x_2173_, v_a_2171_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2177_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2176_, v_a_2175_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v___x_2177_, 0);
lean_dec(v_unused_2185_);
v___x_2179_ = v___x_2177_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_dec(v___x_2177_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_a_2175_);
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2175_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2175_);
v_a_2186_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
return v___x_2174_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v___x_2165_);
lean_dec_ref(v_goal_2150_);
v_a_2194_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2170_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2170_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v___x_2165_);
lean_dec_ref(v_goal_2150_);
v_a_2202_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2168_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2168_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v___x_2165_);
lean_dec_ref(v_goal_2150_);
v_a_2210_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2166_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2166_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_goal_2150_);
v_a_2218_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2220_ = v___x_2158_;
v_isShared_2221_ = v_isSharedCheck_2230_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2158_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2230_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_ref_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v_ref_2222_ = lean_ctor_get(v_a_2154_, 5);
v___x_2223_ = lean_io_error_to_string(v_a_2218_);
v___x_2224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_ofFormat(v___x_2224_);
lean_inc(v_ref_2222_);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_ref_2222_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2226_);
v___x_2228_ = v___x_2220_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2231_, lean_object* v_structId_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2231_, v_structId_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_structId_2232_);
return v_res_2238_;
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

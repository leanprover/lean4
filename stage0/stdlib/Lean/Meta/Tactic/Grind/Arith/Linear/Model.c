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
lean_object* v_es_29_; lean_object* v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; lean_object* v_j_34_; lean_object* v___x_35_; 
v_es_29_ = lean_ctor_get(v_x_26_, 0);
v___x_30_ = lean_box(2);
v___x_31_ = ((size_t)5ULL);
v___x_32_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1);
v___x_33_ = lean_usize_land(v_x_27_, v___x_32_);
v_j_34_ = lean_usize_to_nat(v___x_33_);
v___x_35_ = lean_array_get_borrowed(v___x_30_, v_es_29_, v_j_34_);
lean_dec(v_j_34_);
switch(lean_obj_tag(v___x_35_))
{
case 0:
{
lean_object* v_key_36_; lean_object* v_val_37_; uint8_t v___x_38_; 
v_key_36_ = lean_ctor_get(v___x_35_, 0);
v_val_37_ = lean_ctor_get(v___x_35_, 1);
v___x_38_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_28_, v_key_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
else
{
lean_object* v___x_40_; 
lean_inc(v_val_37_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_val_37_);
return v___x_40_;
}
}
case 1:
{
lean_object* v_node_41_; size_t v___x_42_; 
v_node_41_ = lean_ctor_get(v___x_35_, 0);
v___x_42_ = lean_usize_shift_right(v_x_27_, v___x_31_);
v_x_26_ = v_node_41_;
v_x_27_ = v___x_42_;
goto _start;
}
default: 
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
}
else
{
lean_object* v_ks_45_; lean_object* v_vs_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_ks_45_ = lean_ctor_get(v_x_26_, 0);
v_vs_46_ = lean_ctor_get(v_x_26_, 1);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_ks_45_, v_vs_46_, v___x_47_, v_x_28_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
size_t v_x_335__boxed_52_; lean_object* v_res_53_; 
v_x_335__boxed_52_ = lean_unbox_usize(v_x_50_);
lean_dec(v_x_50_);
v_res_53_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_49_, v_x_335__boxed_52_, v_x_51_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_49_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint64_t v___x_56_; size_t v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_55_);
v___x_57_ = lean_uint64_to_usize(v___x_56_);
v___x_58_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_54_, v___x_57_, v_x_55_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_59_, v_x_60_);
lean_dec_ref(v_x_60_);
lean_dec_ref(v_x_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object* v_s_62_, lean_object* v_e_63_){
_start:
{
lean_object* v_varMap_64_; lean_object* v_assignment_65_; lean_object* v___x_66_; 
v_varMap_64_ = lean_ctor_get(v_s_62_, 31);
v_assignment_65_ = lean_ctor_get(v_s_62_, 35);
v___x_66_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_64_, v_e_63_);
if (lean_obj_tag(v___x_66_) == 1)
{
lean_object* v_val_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_79_; 
v_val_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_79_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_val_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_size_71_; uint8_t v___x_72_; 
v_size_71_ = lean_ctor_get(v_assignment_65_, 2);
v___x_72_ = lean_nat_dec_lt(v_val_67_, v_size_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_del_object(v___x_69_);
lean_dec(v_val_67_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = l_instInhabitedRat;
v___x_75_ = l_Lean_PersistentArray_get_x21___redArg(v___x_74_, v_assignment_65_, v_val_67_);
lean_dec(v_val_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_75_);
v___x_77_ = v___x_69_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v___x_66_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object* v_s_81_, lean_object* v_e_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_81_, v_e_82_);
lean_dec_ref(v_e_82_);
lean_dec_ref(v_s_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object* v_00_u03b2_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_85_, v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object* v_00_u03b2_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_88_, v_x_89_, v_x_90_);
lean_dec_ref(v_x_90_);
lean_dec_ref(v_x_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object* v_00_u03b2_92_, lean_object* v_x_93_, size_t v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_93_, v_x_94_, v_x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
size_t v_x_436__boxed_101_; lean_object* v_res_102_; 
v_x_436__boxed_101_ = lean_unbox_usize(v_x_99_);
lean_dec(v_x_99_);
v_res_102_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_97_, v_x_98_, v_x_436__boxed_101_, v_x_100_);
lean_dec_ref(v_x_100_);
lean_dec_ref(v_x_98_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_103_, lean_object* v_keys_104_, lean_object* v_vals_105_, lean_object* v_heq_106_, lean_object* v_i_107_, lean_object* v_k_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_104_, v_vals_105_, v_i_107_, v_k_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_110_, lean_object* v_keys_111_, lean_object* v_vals_112_, lean_object* v_heq_113_, lean_object* v_i_114_, lean_object* v_k_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_110_, v_keys_111_, v_vals_112_, v_heq_113_, v_i_114_, v_k_115_);
lean_dec_ref(v_k_115_);
lean_dec_ref(v_vals_112_);
lean_dec_ref(v_keys_111_);
return v_res_116_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0(void){
_start:
{
uint8_t v___x_117_; uint64_t v___x_118_; 
v___x_117_ = 1;
v___x_118_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_119_, lean_object* v_n_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_self_126_; lean_object* v___x_127_; uint8_t v_foApprox_128_; uint8_t v_ctxApprox_129_; uint8_t v_quasiPatternApprox_130_; uint8_t v_constApprox_131_; uint8_t v_isDefEqStuckEx_132_; uint8_t v_unificationHints_133_; uint8_t v_proofIrrelevance_134_; uint8_t v_assignSyntheticOpaque_135_; uint8_t v_offsetCnstrs_136_; uint8_t v_etaStruct_137_; uint8_t v_univApprox_138_; uint8_t v_iota_139_; uint8_t v_beta_140_; uint8_t v_proj_141_; uint8_t v_zeta_142_; uint8_t v_zetaDelta_143_; uint8_t v_zetaUnused_144_; uint8_t v_zetaHave_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_182_; 
v_self_126_ = lean_ctor_get(v_n_120_, 0);
lean_inc_ref(v_self_126_);
lean_dec_ref(v_n_120_);
v___x_127_ = l_Lean_Meta_Context_config(v_a_121_);
v_foApprox_128_ = lean_ctor_get_uint8(v___x_127_, 0);
v_ctxApprox_129_ = lean_ctor_get_uint8(v___x_127_, 1);
v_quasiPatternApprox_130_ = lean_ctor_get_uint8(v___x_127_, 2);
v_constApprox_131_ = lean_ctor_get_uint8(v___x_127_, 3);
v_isDefEqStuckEx_132_ = lean_ctor_get_uint8(v___x_127_, 4);
v_unificationHints_133_ = lean_ctor_get_uint8(v___x_127_, 5);
v_proofIrrelevance_134_ = lean_ctor_get_uint8(v___x_127_, 6);
v_assignSyntheticOpaque_135_ = lean_ctor_get_uint8(v___x_127_, 7);
v_offsetCnstrs_136_ = lean_ctor_get_uint8(v___x_127_, 8);
v_etaStruct_137_ = lean_ctor_get_uint8(v___x_127_, 10);
v_univApprox_138_ = lean_ctor_get_uint8(v___x_127_, 11);
v_iota_139_ = lean_ctor_get_uint8(v___x_127_, 12);
v_beta_140_ = lean_ctor_get_uint8(v___x_127_, 13);
v_proj_141_ = lean_ctor_get_uint8(v___x_127_, 14);
v_zeta_142_ = lean_ctor_get_uint8(v___x_127_, 15);
v_zetaDelta_143_ = lean_ctor_get_uint8(v___x_127_, 16);
v_zetaUnused_144_ = lean_ctor_get_uint8(v___x_127_, 17);
v_zetaHave_145_ = lean_ctor_get_uint8(v___x_127_, 18);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_182_ == 0)
{
v___x_147_ = v___x_127_;
v_isShared_148_ = v_isSharedCheck_182_;
goto v_resetjp_146_;
}
else
{
lean_dec(v___x_127_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_182_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v_trackZetaDelta_149_; lean_object* v_zetaDeltaSet_150_; lean_object* v_lctx_151_; lean_object* v_localInstances_152_; lean_object* v_defEqCtx_x3f_153_; lean_object* v_synthPendingDepth_154_; lean_object* v_canUnfold_x3f_155_; uint8_t v_univApprox_156_; uint8_t v_inTypeClassResolution_157_; uint8_t v_cacheInferType_158_; uint8_t v___x_159_; lean_object* v_config_161_; 
v_trackZetaDelta_149_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*7);
v_zetaDeltaSet_150_ = lean_ctor_get(v_a_121_, 1);
v_lctx_151_ = lean_ctor_get(v_a_121_, 2);
v_localInstances_152_ = lean_ctor_get(v_a_121_, 3);
v_defEqCtx_x3f_153_ = lean_ctor_get(v_a_121_, 4);
v_synthPendingDepth_154_ = lean_ctor_get(v_a_121_, 5);
v_canUnfold_x3f_155_ = lean_ctor_get(v_a_121_, 6);
v_univApprox_156_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_157_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*7 + 2);
v_cacheInferType_158_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*7 + 3);
v___x_159_ = 1;
if (v_isShared_148_ == 0)
{
v_config_161_ = v___x_147_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 0, v_foApprox_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 1, v_ctxApprox_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 2, v_quasiPatternApprox_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 3, v_constApprox_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 4, v_isDefEqStuckEx_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 5, v_unificationHints_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 6, v_proofIrrelevance_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 7, v_assignSyntheticOpaque_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 8, v_offsetCnstrs_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 10, v_etaStruct_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 11, v_univApprox_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 12, v_iota_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 13, v_beta_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 14, v_proj_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 15, v_zeta_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 16, v_zetaDelta_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 17, v_zetaUnused_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_181_, 18, v_zetaHave_145_);
v_config_161_ = v_reuseFailAlloc_181_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v_key_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_ctor_set_uint8(v_config_161_, 9, v___x_159_);
v___x_162_ = l_Lean_Meta_Context_configKey(v_a_121_);
v___x_163_ = 2ULL;
v___x_164_ = lean_uint64_shift_right(v___x_162_, v___x_163_);
v___x_165_ = lean_uint64_shift_left(v___x_164_, v___x_163_);
v___x_166_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
v_key_167_ = lean_uint64_lor(v___x_165_, v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_168_, 0, v_config_161_);
lean_ctor_set_uint64(v___x_168_, sizeof(void*)*1, v_key_167_);
lean_inc(v_canUnfold_x3f_155_);
lean_inc(v_synthPendingDepth_154_);
lean_inc(v_defEqCtx_x3f_153_);
lean_inc_ref(v_localInstances_152_);
lean_inc_ref(v_lctx_151_);
lean_inc(v_zetaDeltaSet_150_);
v___x_169_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_zetaDeltaSet_150_);
lean_ctor_set(v___x_169_, 2, v_lctx_151_);
lean_ctor_set(v___x_169_, 3, v_localInstances_152_);
lean_ctor_set(v___x_169_, 4, v_defEqCtx_x3f_153_);
lean_ctor_set(v___x_169_, 5, v_synthPendingDepth_154_);
lean_ctor_set(v___x_169_, 6, v_canUnfold_x3f_155_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7, v_trackZetaDelta_149_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 1, v_univApprox_156_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 2, v_inTypeClassResolution_157_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 3, v_cacheInferType_158_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
lean_inc(v_a_122_);
lean_inc_ref(v___x_169_);
v___x_170_ = lean_infer_type(v_self_126_, v___x_169_, v_a_122_, v_a_123_, v_a_124_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_Meta_isExprDefEq(v_a_171_, v_type_119_, v___x_169_, v_a_122_, v_a_123_, v_a_124_);
lean_dec_ref(v___x_169_);
return v___x_172_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v___x_169_);
lean_dec_ref(v_type_119_);
v_a_173_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_170_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_170_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_183_, lean_object* v_n_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_183_, v_n_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = l_Lean_Expr_cleanupAnnotations(v_e_202_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v___x_203_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_arg_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_arg_206_ = lean_ctor_get(v___x_203_, 1);
lean_inc_ref(v_arg_206_);
v___x_207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v___x_207_);
lean_dec_ref(v_arg_206_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = l_Lean_Expr_isApp(v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
lean_dec_ref(v___x_210_);
lean_dec_ref(v_arg_206_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_210_);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_215_ = l_Lean_Expr_isConstOf(v___x_213_, v___x_214_);
lean_dec_ref(v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_arg_206_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_arg_206_);
return v___x_217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Rat_ofInt(v_a_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_nat_to_int(v_a_220_);
v___x_222_ = l_Rat_ofInt(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_key_226_; lean_object* v_value_227_; lean_object* v_tail_228_; uint8_t v___x_229_; 
v_key_226_ = lean_ctor_get(v_x_224_, 0);
v_value_227_ = lean_ctor_get(v_x_224_, 1);
v_tail_228_ = lean_ctor_get(v_x_224_, 2);
v___x_229_ = lean_expr_eqv(v_key_226_, v_a_223_);
if (v___x_229_ == 0)
{
v_x_224_ = v_tail_228_;
goto _start;
}
else
{
lean_object* v___x_231_; 
lean_inc(v_value_227_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_value_227_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_232_, v_x_233_);
lean_dec(v_x_233_);
lean_dec_ref(v_a_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_buckets_237_; lean_object* v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v_fold_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_buckets_237_ = lean_ctor_get(v_m_235_, 1);
v___x_238_ = lean_array_get_size(v_buckets_237_);
v___x_239_ = l_Lean_Expr_hash(v_a_236_);
v___x_240_ = 32ULL;
v___x_241_ = lean_uint64_shift_right(v___x_239_, v___x_240_);
v_fold_242_ = lean_uint64_xor(v___x_239_, v___x_241_);
v___x_243_ = 16ULL;
v___x_244_ = lean_uint64_shift_right(v_fold_242_, v___x_243_);
v___x_245_ = lean_uint64_xor(v_fold_242_, v___x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
v___x_247_ = lean_usize_of_nat(v___x_238_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v___x_247_, v___x_248_);
v___x_250_ = lean_usize_land(v___x_246_, v___x_249_);
v___x_251_ = lean_array_uget_borrowed(v_buckets_237_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_236_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_253_, v_a_254_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_m_253_);
return v_res_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_295_, lean_object* v_model_296_, lean_object* v_e_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_296_, v_e_297_);
if (lean_obj_tag(v___x_303_) == 1)
{
lean_object* v___x_304_; 
lean_dec_ref(v_e_297_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v___x_303_);
v___x_305_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_297_, v_a_299_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_559_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_559_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_559_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_559_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = l_Lean_Expr_cleanupAnnotations(v_a_306_);
v___x_316_ = l_Lean_Expr_isApp(v___x_315_);
if (v___x_316_ == 0)
{
lean_dec_ref(v___x_315_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_arg_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_arg_317_);
v___x_318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_315_);
v___x_319_ = l_Lean_Expr_isApp(v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref(v___x_318_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_arg_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc_ref(v_arg_320_);
v___x_321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_318_);
v___x_322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_323_ = l_Lean_Expr_isConstOf(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_324_ == 0)
{
lean_dec_ref(v___x_321_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_arg_325_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_325_);
v___x_326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_326_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_331_ == 0)
{
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_333_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
v___x_335_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_340_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_343_);
lean_dec_ref(v___x_336_);
if (v___x_344_ == 0)
{
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
uint8_t v___x_345_; 
lean_del_object(v___x_308_);
v___x_345_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_295_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
if (lean_obj_tag(v_a_349_) == 0)
{
lean_dec_ref(v_arg_317_);
return v___x_348_;
}
else
{
lean_object* v_val_350_; lean_object* v___x_351_; 
lean_dec_ref(v___x_348_);
v_val_350_ = lean_ctor_get(v_a_349_, 0);
lean_inc(v_val_350_);
lean_dec_ref(v_a_349_);
v___x_351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
if (lean_obj_tag(v_a_352_) == 0)
{
lean_dec(v_val_350_);
return v___x_351_;
}
else
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_368_; 
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_369_);
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_368_;
goto v_resetjp_353_;
}
else
{
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_368_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_367_; 
v_val_356_ = lean_ctor_get(v_a_352_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_367_ == 0)
{
v___x_358_ = v_a_352_;
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_dec(v_a_352_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = l_Rat_add(v_val_350_, v_val_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_362_);
v___x_364_ = v___x_354_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
else
{
lean_dec(v_val_350_);
return v___x_351_;
}
}
}
else
{
lean_dec_ref(v_arg_317_);
return v___x_348_;
}
}
}
}
else
{
uint8_t v___x_370_; 
lean_dec_ref(v___x_336_);
lean_del_object(v___x_308_);
v___x_370_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_295_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
if (lean_obj_tag(v_a_374_) == 0)
{
lean_dec_ref(v_arg_317_);
return v___x_373_;
}
else
{
lean_object* v_val_375_; lean_object* v___x_376_; 
lean_dec_ref(v___x_373_);
v_val_375_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_375_);
lean_dec_ref(v_a_374_);
v___x_376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
if (lean_obj_tag(v_a_377_) == 0)
{
lean_dec(v_val_375_);
return v___x_376_;
}
else
{
lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_393_; 
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_376_, 0);
lean_dec(v_unused_394_);
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
else
{
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_392_; 
v_val_381_ = lean_ctor_get(v_a_377_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_377_);
if (v_isSharedCheck_392_ == 0)
{
v___x_383_ = v_a_377_;
v_isShared_384_ = v_isSharedCheck_392_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v_a_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_392_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Rat_sub(v_val_375_, v_val_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_387_);
v___x_389_ = v___x_379_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
else
{
lean_dec(v_val_375_);
return v___x_376_;
}
}
}
else
{
lean_dec_ref(v_arg_317_);
return v___x_373_;
}
}
}
}
else
{
uint8_t v___x_395_; 
lean_dec_ref(v___x_336_);
lean_del_object(v___x_308_);
v___x_395_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_295_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
if (lean_obj_tag(v_a_399_) == 0)
{
lean_dec_ref(v_arg_317_);
return v___x_398_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_401_; 
lean_dec_ref(v___x_398_);
v_val_400_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_a_399_);
v___x_401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
if (lean_obj_tag(v_a_402_) == 0)
{
lean_dec(v_val_400_);
return v___x_401_;
}
else
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_418_; 
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_419_);
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_418_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_418_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_417_; 
v_val_406_ = lean_ctor_get(v_a_402_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_402_);
if (v_isSharedCheck_417_ == 0)
{
v___x_408_ = v_a_402_;
v_isShared_409_ = v_isSharedCheck_417_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v_a_402_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_417_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = l_Rat_mul(v_val_400_, v_val_406_);
lean_dec(v_val_400_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_412_);
v___x_414_ = v___x_404_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
else
{
lean_dec(v_val_400_);
return v___x_401_;
}
}
}
else
{
lean_dec_ref(v_arg_317_);
return v___x_398_;
}
}
}
}
else
{
uint8_t v___x_420_; 
lean_dec_ref(v___x_336_);
lean_del_object(v___x_308_);
v___x_420_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_295_, v_arg_325_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; 
v___x_421_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_295_, v_arg_325_);
lean_dec_ref(v_arg_325_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_getNatValue_x3f(v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec_ref(v_arg_320_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_454_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_454_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
if (lean_obj_tag(v_a_425_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec_ref(v_arg_317_);
v___x_429_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
lean_del_object(v___x_427_);
v_val_433_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_val_433_);
lean_dec_ref(v_a_425_);
v___x_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
if (lean_obj_tag(v_a_435_) == 0)
{
lean_dec(v_val_433_);
return v___x_434_;
}
else
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_452_; 
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v___x_434_, 0);
lean_dec(v_unused_453_);
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_452_;
goto v_resetjp_436_;
}
else
{
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_452_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_val_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_451_; 
v_val_439_ = lean_ctor_get(v_a_435_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_a_435_);
if (v_isSharedCheck_451_ == 0)
{
v___x_441_ = v_a_435_;
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_val_439_);
lean_dec(v_a_435_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_433_);
v___x_444_ = l_Rat_mul(v___x_443_, v_val_439_);
lean_dec_ref(v___x_443_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_450_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_446_);
v___x_448_ = v___x_437_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
else
{
lean_dec(v_val_433_);
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_arg_317_);
v_a_455_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_424_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_424_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec_ref(v_arg_325_);
v___x_463_ = l_Lean_Meta_getIntValue_x3f(v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_493_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_493_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_493_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_493_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
if (lean_obj_tag(v_a_464_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec_ref(v_arg_317_);
v___x_468_ = lean_box(0);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
lean_del_object(v___x_466_);
v_val_472_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v_a_464_);
v___x_473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
if (lean_obj_tag(v_a_474_) == 0)
{
lean_dec(v_val_472_);
return v___x_473_;
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_491_; 
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v___x_473_, 0);
lean_dec(v_unused_492_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_490_; 
v_val_478_ = lean_ctor_get(v_a_474_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_490_ == 0)
{
v___x_480_ = v_a_474_;
v_isShared_481_ = v_isSharedCheck_490_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_a_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_490_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_482_ = l_Rat_ofInt(v_val_472_);
v___x_483_ = l_Rat_mul(v___x_482_, v_val_478_);
lean_dec_ref(v___x_482_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_485_);
v___x_487_ = v___x_476_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
else
{
lean_dec(v_val_472_);
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_arg_317_);
v_a_494_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_463_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_463_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
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
uint8_t v___x_502_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_del_object(v___x_308_);
v___x_502_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_295_, v_arg_320_);
lean_dec_ref(v_arg_320_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_arg_317_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_295_, v_model_296_, v_arg_317_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
if (lean_obj_tag(v_a_506_) == 0)
{
return v___x_505_;
}
else
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_522_; 
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_505_, 0);
lean_dec(v_unused_523_);
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_val_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_521_; 
v_val_510_ = lean_ctor_get(v_a_506_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_521_ == 0)
{
v___x_512_ = v_a_506_;
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_val_510_);
lean_dec(v_a_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = l_Rat_neg(v_val_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_516_);
v___x_518_ = v___x_508_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
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
else
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v___x_524_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_325_);
lean_dec_ref(v_arg_317_);
lean_del_object(v___x_308_);
v___x_524_ = l_Lean_Meta_getNatValue_x3f(v_arg_320_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec_ref(v_arg_320_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_545_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_545_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_545_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
if (lean_obj_tag(v_a_525_) == 0)
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_val_533_ = lean_ctor_get(v_a_525_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v_a_525_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_a_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_539_);
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_524_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_524_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
else
{
uint8_t v___x_554_; 
lean_dec_ref(v___x_321_);
lean_dec_ref(v_arg_320_);
lean_del_object(v___x_308_);
v___x_554_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_295_, v_arg_317_);
lean_dec_ref(v_arg_317_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_305_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_305_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_568_, lean_object* v_model_569_, lean_object* v_e_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_568_, v_model_569_, v_e_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_model_569_);
lean_dec_ref(v_s_568_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_577_, lean_object* v_m_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_581_, lean_object* v_m_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_581_, v_m_582_, v_a_583_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_m_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_nat_to_int(v_a_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_587_, lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_591_, lean_object* v_a_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_591_, v_a_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_595_, lean_object* v_s_596_, lean_object* v_model_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_596_, v_model_597_, v_e_595_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_604_, lean_object* v_s_605_, lean_object* v_model_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_604_, v_s_605_, v_model_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec_ref(v_model_606_);
lean_dec_ref(v_s_605_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
else
{
lean_object* v_key_616_; lean_object* v_tail_617_; uint8_t v___x_618_; 
v_key_616_ = lean_ctor_get(v_x_614_, 0);
v_tail_617_ = lean_ctor_get(v_x_614_, 2);
v___x_618_ = lean_expr_eqv(v_key_616_, v_a_613_);
if (v___x_618_ == 0)
{
v_x_614_ = v_tail_617_;
goto _start;
}
else
{
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_620_, lean_object* v_x_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_620_, v_x_621_);
lean_dec(v_x_621_);
lean_dec_ref(v_a_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_buckets_626_; lean_object* v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v___x_630_; uint64_t v_fold_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_buckets_626_ = lean_ctor_get(v_m_624_, 1);
v___x_627_ = lean_array_get_size(v_buckets_626_);
v___x_628_ = l_Lean_Expr_hash(v_a_625_);
v___x_629_ = 32ULL;
v___x_630_ = lean_uint64_shift_right(v___x_628_, v___x_629_);
v_fold_631_ = lean_uint64_xor(v___x_628_, v___x_630_);
v___x_632_ = 16ULL;
v___x_633_ = lean_uint64_shift_right(v_fold_631_, v___x_632_);
v___x_634_ = lean_uint64_xor(v_fold_631_, v___x_633_);
v___x_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = lean_usize_of_nat(v___x_627_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_sub(v___x_636_, v___x_637_);
v___x_639_ = lean_usize_land(v___x_635_, v___x_638_);
v___x_640_ = lean_array_uget_borrowed(v_buckets_626_, v___x_639_);
v___x_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_625_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_642_, v_a_643_);
lean_dec_ref(v_a_643_);
lean_dec_ref(v_m_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v___x_646_, lean_object* v_goal_647_, lean_object* v_structId_648_, lean_object* v_as_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_b_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_b_652_);
return v___x_659_;
}
else
{
lean_object* v_snd_660_; lean_object* v_a_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_692_; 
v_snd_660_ = lean_ctor_get(v_b_652_, 1);
lean_inc(v_snd_660_);
lean_dec_ref(v_b_652_);
v_a_661_ = lean_array_uget(v_as_649_, v_i_651_);
v_fst_662_ = lean_ctor_get(v_a_661_, 0);
v_snd_663_ = lean_ctor_get(v_a_661_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_661_);
if (v_isSharedCheck_692_ == 0)
{
v___x_665_ = v_a_661_;
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_a_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_a_669_; uint8_t v___y_677_; uint8_t v___x_690_; 
v___x_667_ = lean_box(0);
v___x_690_ = lean_nat_dec_eq(v_structId_648_, v_snd_663_);
lean_dec(v_snd_663_);
if (v___x_690_ == 0)
{
v___y_677_ = v___x_690_;
goto v___jp_676_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_660_, v_fst_662_);
if (v___x_691_ == 0)
{
v___y_677_ = v___x_690_;
goto v___jp_676_;
}
else
{
lean_dec(v_fst_662_);
v_a_669_ = v_snd_660_;
goto v___jp_668_;
}
}
v___jp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_a_669_);
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_a_669_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
size_t v___x_672_; size_t v___x_673_; 
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_651_, v___x_672_);
v_i_651_ = v___x_673_;
v_b_652_ = v___x_671_;
goto _start;
}
}
v___jp_676_:
{
if (v___y_677_ == 0)
{
lean_dec(v_fst_662_);
v_a_669_ = v_snd_660_;
goto v___jp_668_;
}
else
{
lean_object* v___x_678_; 
lean_inc(v_fst_662_);
v___x_678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_646_, v_snd_660_, v_fst_662_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v___x_678_);
if (lean_obj_tag(v_a_679_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_681_; 
v_val_680_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v_a_679_);
v___x_681_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_647_, v_fst_662_, v_val_680_, v_snd_660_);
v_a_669_ = v___x_681_;
goto v___jp_668_;
}
else
{
lean_dec(v_a_679_);
lean_dec(v_fst_662_);
v_a_669_ = v_snd_660_;
goto v___jp_668_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_665_);
lean_dec(v_fst_662_);
lean_dec(v_snd_660_);
v_a_682_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_678_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v___x_693_, lean_object* v_goal_694_, lean_object* v_structId_695_, lean_object* v_as_696_, lean_object* v_sz_697_, lean_object* v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
size_t v_sz_boxed_705_; size_t v_i_boxed_706_; lean_object* v_res_707_; 
v_sz_boxed_705_ = lean_unbox_usize(v_sz_697_);
lean_dec(v_sz_697_);
v_i_boxed_706_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_693_, v_goal_694_, v_structId_695_, v_as_696_, v_sz_boxed_705_, v_i_boxed_706_, v_b_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_as_696_);
lean_dec(v_structId_695_);
lean_dec_ref(v_goal_694_);
lean_dec_ref(v___x_693_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v___x_708_, lean_object* v_goal_709_, lean_object* v_structId_710_, lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_b_714_);
return v___x_721_;
}
else
{
lean_object* v_snd_722_; lean_object* v_a_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_754_; 
v_snd_722_ = lean_ctor_get(v_b_714_, 1);
lean_inc(v_snd_722_);
lean_dec_ref(v_b_714_);
v_a_723_ = lean_array_uget(v_as_711_, v_i_713_);
v_fst_724_ = lean_ctor_get(v_a_723_, 0);
v_snd_725_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_754_ == 0)
{
v___x_727_ = v_a_723_;
v_isShared_728_ = v_isSharedCheck_754_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_a_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_754_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v_a_731_; uint8_t v___y_739_; uint8_t v___x_752_; 
v___x_729_ = lean_box(0);
v___x_752_ = lean_nat_dec_eq(v_structId_710_, v_snd_725_);
lean_dec(v_snd_725_);
if (v___x_752_ == 0)
{
v___y_739_ = v___x_752_;
goto v___jp_738_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_722_, v_fst_724_);
if (v___x_753_ == 0)
{
v___y_739_ = v___x_752_;
goto v___jp_738_;
}
else
{
lean_dec(v_fst_724_);
v_a_731_ = v_snd_722_;
goto v___jp_730_;
}
}
v___jp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_a_731_);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_731_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_713_, v___x_734_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_708_, v_goal_709_, v_structId_710_, v_as_711_, v_sz_712_, v___x_735_, v___x_733_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_736_;
}
}
v___jp_738_:
{
if (v___y_739_ == 0)
{
lean_dec(v_fst_724_);
v_a_731_ = v_snd_722_;
goto v___jp_730_;
}
else
{
lean_object* v___x_740_; 
lean_inc(v_fst_724_);
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_708_, v_snd_722_, v_fst_724_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_740_);
if (lean_obj_tag(v_a_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_743_; 
v_val_742_ = lean_ctor_get(v_a_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref(v_a_741_);
v___x_743_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_709_, v_fst_724_, v_val_742_, v_snd_722_);
v_a_731_ = v___x_743_;
goto v___jp_730_;
}
else
{
lean_dec(v_a_741_);
lean_dec(v_fst_724_);
v_a_731_ = v_snd_722_;
goto v___jp_730_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_727_);
lean_dec(v_fst_724_);
lean_dec(v_snd_722_);
v_a_744_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_740_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v___x_755_, lean_object* v_goal_756_, lean_object* v_structId_757_, lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_768_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_755_, v_goal_756_, v_structId_757_, v_as_758_, v_sz_boxed_767_, v_i_boxed_768_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_758_);
lean_dec(v_structId_757_);
lean_dec_ref(v_goal_756_);
lean_dec_ref(v___x_755_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_770_, lean_object* v___x_771_, lean_object* v_goal_772_, lean_object* v_structId_773_, lean_object* v_n_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
if (lean_obj_tag(v_n_774_) == 0)
{
lean_object* v_cs_781_; lean_object* v___x_782_; lean_object* v___x_783_; size_t v_sz_784_; size_t v___x_785_; lean_object* v___x_786_; 
v_cs_781_ = lean_ctor_get(v_n_774_, 0);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_b_775_);
v_sz_784_ = lean_array_size(v_cs_781_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_770_, v___x_771_, v_goal_772_, v_structId_773_, v_cs_781_, v_sz_784_, v___x_785_, v___x_783_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_801_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_801_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_fst_791_; 
v_fst_791_ = lean_ctor_get(v_a_787_, 0);
if (lean_obj_tag(v_fst_791_) == 0)
{
lean_object* v_snd_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v_snd_792_ = lean_ctor_get(v_a_787_, 1);
lean_inc(v_snd_792_);
lean_dec(v_a_787_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_snd_792_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_793_);
v___x_795_ = v___x_789_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; 
lean_inc_ref(v_fst_791_);
lean_dec(v_a_787_);
v_val_797_ = lean_ctor_get(v_fst_791_, 0);
lean_inc(v_val_797_);
lean_dec_ref(v_fst_791_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_val_797_);
v___x_799_ = v___x_789_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_786_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_786_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_vs_810_; lean_object* v___x_811_; lean_object* v___x_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_vs_810_ = lean_ctor_get(v_n_774_, 0);
v___x_811_ = lean_box(0);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_b_775_);
v_sz_813_ = lean_array_size(v_vs_810_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_771_, v_goal_772_, v_structId_773_, v_vs_810_, v_sz_813_, v___x_814_, v___x_812_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_830_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_830_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_fst_820_; 
v_fst_820_ = lean_ctor_get(v_a_816_, 0);
if (lean_obj_tag(v_fst_820_) == 0)
{
lean_object* v_snd_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v_snd_821_ = lean_ctor_get(v_a_816_, 1);
lean_inc(v_snd_821_);
lean_dec(v_a_816_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_snd_821_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; 
lean_inc_ref(v_fst_820_);
lean_dec(v_a_816_);
v_val_826_ = lean_ctor_get(v_fst_820_, 0);
lean_inc(v_val_826_);
lean_dec_ref(v_fst_820_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_val_826_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_val_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_815_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_815_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_839_, lean_object* v___x_840_, lean_object* v_goal_841_, lean_object* v_structId_842_, lean_object* v_as_843_, size_t v_sz_844_, size_t v_i_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_845_, v_sz_844_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_b_846_);
return v___x_853_;
}
else
{
lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_888_; 
v_snd_854_ = lean_ctor_get(v_b_846_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_b_846_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_b_846_, 0);
lean_dec(v_unused_889_);
v___x_856_ = v_b_846_;
v_isShared_857_ = v_isSharedCheck_888_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_dec(v_b_846_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_888_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_array_uget_borrowed(v_as_843_, v_i_845_);
lean_inc(v_snd_854_);
v___x_859_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_839_, v___x_840_, v_goal_841_, v_structId_842_, v_a_858_, v_snd_854_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_879_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_879_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_879_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_879_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_a_860_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_864_);
v___x_866_ = v___x_856_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_854_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_del_object(v___x_862_);
lean_dec(v_snd_854_);
v_a_871_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v_a_860_);
v___x_872_ = lean_box(0);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_a_871_);
lean_ctor_set(v___x_856_, 0, v___x_872_);
v___x_874_ = v___x_856_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_a_871_);
v___x_874_ = v_reuseFailAlloc_878_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
size_t v___x_875_; size_t v___x_876_; 
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_845_, v___x_875_);
v_i_845_ = v___x_876_;
v_b_846_ = v___x_874_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_854_);
v_a_880_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_859_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_859_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_890_, lean_object* v___x_891_, lean_object* v_goal_892_, lean_object* v_structId_893_, lean_object* v_as_894_, lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_b_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
size_t v_sz_boxed_903_; size_t v_i_boxed_904_; lean_object* v_res_905_; 
v_sz_boxed_903_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_904_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_890_, v___x_891_, v_goal_892_, v_structId_893_, v_as_894_, v_sz_boxed_903_, v_i_boxed_904_, v_b_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec_ref(v_as_894_);
lean_dec(v_structId_893_);
lean_dec_ref(v_goal_892_);
lean_dec_ref(v___x_891_);
lean_dec_ref(v_init_890_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_906_, lean_object* v___x_907_, lean_object* v_goal_908_, lean_object* v_structId_909_, lean_object* v_n_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_906_, v___x_907_, v_goal_908_, v_structId_909_, v_n_910_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_n_910_);
lean_dec(v_structId_909_);
lean_dec_ref(v_goal_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_init_906_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v___x_918_, lean_object* v_goal_919_, lean_object* v_structId_920_, lean_object* v_as_921_, size_t v_sz_922_, size_t v_i_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_lt(v_i_923_, v_sz_922_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v_b_924_);
return v___x_931_;
}
else
{
lean_object* v_snd_932_; lean_object* v_a_933_; lean_object* v_fst_934_; lean_object* v_snd_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_964_; 
v_snd_932_ = lean_ctor_get(v_b_924_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v_b_924_);
v_a_933_ = lean_array_uget(v_as_921_, v_i_923_);
v_fst_934_ = lean_ctor_get(v_a_933_, 0);
v_snd_935_ = lean_ctor_get(v_a_933_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_964_ == 0)
{
v___x_937_ = v_a_933_;
v_isShared_938_ = v_isSharedCheck_964_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_935_);
lean_inc(v_fst_934_);
lean_dec(v_a_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_964_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v_a_941_; uint8_t v___y_949_; uint8_t v___x_962_; 
v___x_939_ = lean_box(0);
v___x_962_ = lean_nat_dec_eq(v_structId_920_, v_snd_935_);
lean_dec(v_snd_935_);
if (v___x_962_ == 0)
{
v___y_949_ = v___x_962_;
goto v___jp_948_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_932_, v_fst_934_);
if (v___x_963_ == 0)
{
v___y_949_ = v___x_962_;
goto v___jp_948_;
}
else
{
lean_dec(v_fst_934_);
v_a_941_ = v_snd_932_;
goto v___jp_940_;
}
}
v___jp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v_a_941_);
lean_ctor_set(v___x_937_, 0, v___x_939_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_941_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_923_, v___x_944_);
v_i_923_ = v___x_945_;
v_b_924_ = v___x_943_;
goto _start;
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
lean_dec(v_fst_934_);
v_a_941_ = v_snd_932_;
goto v___jp_940_;
}
else
{
lean_object* v___x_950_; 
lean_inc(v_fst_934_);
v___x_950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_918_, v_snd_932_, v_fst_934_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref(v___x_950_);
if (lean_obj_tag(v_a_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_953_; 
v_val_952_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref(v_a_951_);
v___x_953_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_919_, v_fst_934_, v_val_952_, v_snd_932_);
v_a_941_ = v___x_953_;
goto v___jp_940_;
}
else
{
lean_dec(v_a_951_);
lean_dec(v_fst_934_);
v_a_941_ = v_snd_932_;
goto v___jp_940_;
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_del_object(v___x_937_);
lean_dec(v_fst_934_);
lean_dec(v_snd_932_);
v_a_954_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_950_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v___x_965_, lean_object* v_goal_966_, lean_object* v_structId_967_, lean_object* v_as_968_, lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_978_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_965_, v_goal_966_, v_structId_967_, v_as_968_, v_sz_boxed_977_, v_i_boxed_978_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v_as_968_);
lean_dec(v_structId_967_);
lean_dec_ref(v_goal_966_);
lean_dec_ref(v___x_965_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v___x_980_, lean_object* v_goal_981_, lean_object* v_structId_982_, lean_object* v_as_983_, size_t v_sz_984_, size_t v_i_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
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
lean_object* v_snd_994_; lean_object* v_a_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1026_; 
v_snd_994_ = lean_ctor_get(v_b_986_, 1);
lean_inc(v_snd_994_);
lean_dec_ref(v_b_986_);
v_a_995_ = lean_array_uget(v_as_983_, v_i_985_);
v_fst_996_ = lean_ctor_get(v_a_995_, 0);
v_snd_997_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_999_ = v_a_995_;
v_isShared_1000_ = v_isSharedCheck_1026_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v_a_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1026_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_a_1003_; uint8_t v___y_1011_; uint8_t v___x_1024_; 
v___x_1001_ = lean_box(0);
v___x_1024_ = lean_nat_dec_eq(v_structId_982_, v_snd_997_);
lean_dec(v_snd_997_);
if (v___x_1024_ == 0)
{
v___y_1011_ = v___x_1024_;
goto v___jp_1010_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_994_, v_fst_996_);
if (v___x_1025_ == 0)
{
v___y_1011_ = v___x_1024_;
goto v___jp_1010_;
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
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_980_, v_goal_981_, v_structId_982_, v_as_983_, v_sz_984_, v___x_1007_, v___x_1005_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_1008_;
}
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
lean_dec(v_fst_996_);
v_a_1003_ = v_snd_994_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1012_; 
lean_inc(v_fst_996_);
v___x_1012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_980_, v_snd_994_, v_fst_996_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
if (lean_obj_tag(v_a_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1015_; 
v_val_1014_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref(v_a_1013_);
v___x_1015_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_981_, v_fst_996_, v_val_1014_, v_snd_994_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v___x_1027_, lean_object* v_goal_1028_, lean_object* v_structId_1029_, lean_object* v_as_1030_, lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
size_t v_sz_boxed_1039_; size_t v_i_boxed_1040_; lean_object* v_res_1041_; 
v_sz_boxed_1039_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1027_, v_goal_1028_, v_structId_1029_, v_as_1030_, v_sz_boxed_1039_, v_i_boxed_1040_, v_b_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_as_1030_);
lean_dec(v_structId_1029_);
lean_dec_ref(v_goal_1028_);
lean_dec_ref(v___x_1027_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1042_, lean_object* v_goal_1043_, lean_object* v_structId_1044_, lean_object* v_t_1045_, lean_object* v_init_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_root_1052_; lean_object* v_tail_1053_; lean_object* v___x_1054_; 
v_root_1052_ = lean_ctor_get(v_t_1045_, 0);
v_tail_1053_ = lean_ctor_get(v_t_1045_, 1);
lean_inc_ref(v_init_1046_);
v___x_1054_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1046_, v___x_1042_, v_goal_1043_, v_structId_1044_, v_root_1052_, v_init_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec_ref(v_init_1046_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1091_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1091_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1091_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; 
v_a_1059_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v_a_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v_a_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; size_t v_sz_1066_; size_t v___x_1067_; lean_object* v___x_1068_; 
lean_del_object(v___x_1057_);
v_a_1063_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v_a_1055_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1063_);
v_sz_1066_ = lean_array_size(v_tail_1053_);
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1042_, v_goal_1043_, v_structId_1044_, v_tail_1053_, v_sz_1066_, v___x_1067_, v___x_1065_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1082_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1082_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1082_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_fst_1073_; 
v_fst_1073_ = lean_ctor_get(v_a_1069_, 0);
if (lean_obj_tag(v_fst_1073_) == 0)
{
lean_object* v_snd_1074_; lean_object* v___x_1076_; 
v_snd_1074_ = lean_ctor_get(v_a_1069_, 1);
lean_inc(v_snd_1074_);
lean_dec(v_a_1069_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v_snd_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_snd_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v_val_1078_; lean_object* v___x_1080_; 
lean_inc_ref(v_fst_1073_);
lean_dec(v_a_1069_);
v_val_1078_ = lean_ctor_get(v_fst_1073_, 0);
lean_inc(v_val_1078_);
lean_dec_ref(v_fst_1073_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v_val_1078_);
v___x_1080_ = v___x_1071_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_val_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1068_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1068_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1054_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1054_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1100_, lean_object* v_goal_1101_, lean_object* v_structId_1102_, lean_object* v_t_1103_, lean_object* v_init_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1100_, v_goal_1101_, v_structId_1102_, v_t_1103_, v_init_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_t_1103_);
lean_dec(v_structId_1102_);
lean_dec_ref(v_goal_1101_);
lean_dec_ref(v___x_1100_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1111_, lean_object* v_structId_1112_, lean_object* v_model_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1120_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1119_, v_goal_1111_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_structs_1122_; lean_object* v_exprToStructIdEntries_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
v_structs_1122_ = lean_ctor_get(v_a_1121_, 0);
lean_inc_ref(v_structs_1122_);
v_exprToStructIdEntries_1123_ = lean_ctor_get(v_a_1121_, 3);
lean_inc_ref(v_exprToStructIdEntries_1123_);
lean_dec(v_a_1121_);
v___x_1124_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1125_ = lean_array_get(v___x_1124_, v_structs_1122_, v_structId_1112_);
lean_dec_ref(v_structs_1122_);
v___x_1126_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1125_, v_goal_1111_, v_structId_1112_, v_exprToStructIdEntries_1123_, v_model_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec_ref(v_exprToStructIdEntries_1123_);
lean_dec(v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_model_1113_);
v_a_1127_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1129_ = v___x_1120_;
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1120_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v_ref_1131_ = lean_ctor_get(v_a_1116_, 5);
v___x_1132_ = lean_io_error_to_string(v_a_1127_);
v___x_1133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_ofFormat(v___x_1133_);
lean_inc(v_ref_1131_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_ref_1131_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1135_);
v___x_1137_ = v___x_1129_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1140_, lean_object* v_structId_1141_, lean_object* v_model_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1140_, v_structId_1141_, v_model_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_structId_1141_);
lean_dec_ref(v_goal_1140_);
return v_res_1148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1149_, lean_object* v_m_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1150_, v_a_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1153_, lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
uint8_t v_res_1156_; lean_object* v_r_1157_; 
v_res_1156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1153_, v_m_1154_, v_a_1155_);
lean_dec_ref(v_a_1155_);
lean_dec_ref(v_m_1154_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1158_, lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
uint8_t v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1159_, v_x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1162_, v_a_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec_ref(v_a_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1167_, lean_object* v___x_1168_, lean_object* v_as_1169_, size_t v_sz_1170_, size_t v_i_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1171_, v_sz_1170_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v___x_1168_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1172_);
return v___x_1179_;
}
else
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1221_; 
v_snd_1180_ = lean_ctor_get(v_b_1172_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_b_1172_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_b_1172_, 0);
lean_dec(v_unused_1222_);
v___x_1182_ = v_b_1172_;
v_isShared_1183_ = v_isSharedCheck_1221_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_b_1172_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1221_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_array_uget_borrowed(v_as_1169_, v_i_1171_);
lean_inc(v_a_1184_);
v___x_1185_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1167_, v_a_1184_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v_a_1189_; uint8_t v___x_1196_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = lean_box(0);
v___x_1196_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1186_);
if (v___x_1196_ == 0)
{
lean_dec(v_a_1186_);
v_a_1189_ = v_snd_1180_;
goto v___jp_1188_;
}
else
{
lean_object* v_type_1197_; lean_object* v___x_1198_; 
v_type_1197_ = lean_ctor_get(v___x_1168_, 2);
lean_inc(v_a_1186_);
lean_inc_ref(v_type_1197_);
v___x_1198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1197_, v_a_1186_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_a_1186_);
v_a_1189_ = v_snd_1180_;
goto v___jp_1188_;
}
else
{
lean_object* v_self_1201_; lean_object* v___x_1202_; 
v_self_1201_ = lean_ctor_get(v_a_1186_, 0);
lean_inc_ref(v_self_1201_);
lean_dec(v_a_1186_);
v___x_1202_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1168_, v_self_1201_);
if (lean_obj_tag(v___x_1202_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1204_; 
v_val_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_val_1203_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1167_, v_self_1201_, v_val_1203_, v_snd_1180_);
v_a_1189_ = v___x_1204_;
goto v___jp_1188_;
}
else
{
lean_dec(v___x_1202_);
lean_dec_ref(v_self_1201_);
v_a_1189_ = v_snd_1180_;
goto v___jp_1188_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1186_);
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
lean_dec_ref(v___x_1168_);
v_a_1205_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1198_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1198_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
v___jp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_a_1189_);
lean_ctor_set(v___x_1182_, 0, v___x_1187_);
v___x_1191_ = v___x_1182_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_a_1189_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
size_t v___x_1192_; size_t v___x_1193_; 
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_add(v_i_1171_, v___x_1192_);
v_i_1171_ = v___x_1193_;
v_b_1172_ = v___x_1191_;
goto _start;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
lean_dec_ref(v___x_1168_);
v_a_1213_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1185_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1185_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1223_, lean_object* v___x_1224_, lean_object* v_as_1225_, lean_object* v_sz_1226_, lean_object* v_i_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
size_t v_sz_boxed_1234_; size_t v_i_boxed_1235_; lean_object* v_res_1236_; 
v_sz_boxed_1234_ = lean_unbox_usize(v_sz_1226_);
lean_dec(v_sz_1226_);
v_i_boxed_1235_ = lean_unbox_usize(v_i_1227_);
lean_dec(v_i_1227_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1223_, v___x_1224_, v_as_1225_, v_sz_boxed_1234_, v_i_boxed_1235_, v_b_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_as_1225_);
lean_dec_ref(v_goal_1223_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1237_, lean_object* v___x_1238_, lean_object* v_as_1239_, size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1241_, v_sz_1240_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v___x_1238_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_b_1242_);
return v___x_1249_;
}
else
{
lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1291_; 
v_snd_1250_ = lean_ctor_get(v_b_1242_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_b_1242_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v_b_1242_, 0);
lean_dec(v_unused_1292_);
v___x_1252_ = v_b_1242_;
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_dec(v_b_1242_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1291_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_array_uget_borrowed(v_as_1239_, v_i_1241_);
lean_inc(v_a_1254_);
v___x_1255_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1237_, v_a_1254_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v_a_1259_; uint8_t v___x_1266_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = lean_box(0);
v___x_1266_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1256_);
if (v___x_1266_ == 0)
{
lean_dec(v_a_1256_);
v_a_1259_ = v_snd_1250_;
goto v___jp_1258_;
}
else
{
lean_object* v_type_1267_; lean_object* v___x_1268_; 
v_type_1267_ = lean_ctor_get(v___x_1238_, 2);
lean_inc(v_a_1256_);
lean_inc_ref(v_type_1267_);
v___x_1268_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1267_, v_a_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v_a_1256_);
v_a_1259_ = v_snd_1250_;
goto v___jp_1258_;
}
else
{
lean_object* v_self_1271_; lean_object* v___x_1272_; 
v_self_1271_ = lean_ctor_get(v_a_1256_, 0);
lean_inc_ref(v_self_1271_);
lean_dec(v_a_1256_);
v___x_1272_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1238_, v_self_1271_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1274_; 
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1237_, v_self_1271_, v_val_1273_, v_snd_1250_);
v_a_1259_ = v___x_1274_;
goto v___jp_1258_;
}
else
{
lean_dec(v___x_1272_);
lean_dec_ref(v_self_1271_);
v_a_1259_ = v_snd_1250_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_a_1256_);
lean_del_object(v___x_1252_);
lean_dec(v_snd_1250_);
lean_dec_ref(v___x_1238_);
v_a_1275_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1268_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1268_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_a_1259_);
lean_ctor_set(v___x_1252_, 0, v___x_1257_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1259_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1241_, v___x_1262_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1237_, v___x_1238_, v_as_1239_, v_sz_1240_, v___x_1263_, v___x_1261_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1252_);
lean_dec(v_snd_1250_);
lean_dec_ref(v___x_1238_);
v_a_1283_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1255_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1255_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1293_, lean_object* v___x_1294_, lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1293_, v___x_1294_, v_as_1295_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v_as_1295_);
lean_dec_ref(v_goal_1293_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1307_, lean_object* v_goal_1308_, lean_object* v___x_1309_, lean_object* v_n_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
if (lean_obj_tag(v_n_1310_) == 0)
{
lean_object* v_cs_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v_cs_1317_ = lean_ctor_get(v_n_1310_, 0);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_b_1311_);
v_sz_1320_ = lean_array_size(v_cs_1317_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1307_, v_goal_1308_, v___x_1309_, v_cs_1317_, v_sz_1320_, v___x_1321_, v___x_1319_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1337_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_fst_1327_; 
v_fst_1327_ = lean_ctor_get(v_a_1323_, 0);
if (lean_obj_tag(v_fst_1327_) == 0)
{
lean_object* v_snd_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_snd_1328_ = lean_ctor_get(v_a_1323_, 1);
lean_inc(v_snd_1328_);
lean_dec(v_a_1323_);
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_snd_1328_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1329_);
v___x_1331_ = v___x_1325_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
lean_inc_ref(v_fst_1327_);
lean_dec(v_a_1323_);
v_val_1333_ = lean_ctor_get(v_fst_1327_, 0);
lean_inc(v_val_1333_);
lean_dec_ref(v_fst_1327_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_val_1333_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1322_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1322_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_vs_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_vs_1346_ = lean_ctor_get(v_n_1310_, 0);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_b_1311_);
v_sz_1349_ = lean_array_size(v_vs_1346_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1308_, v___x_1309_, v_vs_1346_, v_sz_1349_, v___x_1350_, v___x_1348_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1366_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fst_1356_; 
v_fst_1356_ = lean_ctor_get(v_a_1352_, 0);
if (lean_obj_tag(v_fst_1356_) == 0)
{
lean_object* v_snd_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v_snd_1357_ = lean_ctor_get(v_a_1352_, 1);
lean_inc(v_snd_1357_);
lean_dec(v_a_1352_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_snd_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1358_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1364_; 
lean_inc_ref(v_fst_1356_);
lean_dec(v_a_1352_);
v_val_1362_ = lean_ctor_get(v_fst_1356_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v_fst_1356_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_val_1362_);
v___x_1364_ = v___x_1354_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_val_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1351_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1351_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1375_, lean_object* v_goal_1376_, lean_object* v___x_1377_, lean_object* v_as_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v___x_1387_; 
v___x_1387_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_dec_ref(v___x_1377_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_b_1381_);
return v___x_1388_;
}
else
{
lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1423_; 
v_snd_1389_ = lean_ctor_get(v_b_1381_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_b_1381_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_b_1381_, 0);
lean_dec(v_unused_1424_);
v___x_1391_ = v_b_1381_;
v_isShared_1392_ = v_isSharedCheck_1423_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_dec(v_b_1381_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1423_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_array_uget_borrowed(v_as_1378_, v_i_1380_);
lean_inc(v_snd_1389_);
lean_inc_ref(v___x_1377_);
v___x_1394_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1375_, v_goal_1376_, v___x_1377_, v_a_1393_, v_snd_1389_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1414_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1414_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1414_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
if (lean_obj_tag(v_a_1395_) == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec_ref(v___x_1377_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1399_);
v___x_1401_ = v___x_1391_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_snd_1389_);
v___x_1401_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_del_object(v___x_1397_);
lean_dec(v_snd_1389_);
v_a_1406_ = lean_ctor_get(v_a_1395_, 0);
lean_inc(v_a_1406_);
lean_dec_ref(v_a_1395_);
v___x_1407_ = lean_box(0);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v_a_1406_);
lean_ctor_set(v___x_1391_, 0, v___x_1407_);
v___x_1409_ = v___x_1391_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_a_1406_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
size_t v___x_1410_; size_t v___x_1411_; 
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1380_, v___x_1410_);
v_i_1380_ = v___x_1411_;
v_b_1381_ = v___x_1409_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1391_);
lean_dec(v_snd_1389_);
lean_dec_ref(v___x_1377_);
v_a_1415_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1394_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1394_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1425_, lean_object* v_goal_1426_, lean_object* v___x_1427_, lean_object* v_as_1428_, lean_object* v_sz_1429_, lean_object* v_i_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1429_);
lean_dec(v_sz_1429_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1425_, v_goal_1426_, v___x_1427_, v_as_1428_, v_sz_boxed_1437_, v_i_boxed_1438_, v_b_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_as_1428_);
lean_dec_ref(v_goal_1426_);
lean_dec_ref(v_init_1425_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1440_, lean_object* v_goal_1441_, lean_object* v___x_1442_, lean_object* v_n_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1440_, v_goal_1441_, v___x_1442_, v_n_1443_, v_b_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v_n_1443_);
lean_dec_ref(v_goal_1441_);
lean_dec_ref(v_init_1440_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1451_, lean_object* v___x_1452_, lean_object* v_as_1453_, size_t v_sz_1454_, size_t v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1455_, v_sz_1454_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec_ref(v___x_1452_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1456_);
return v___x_1463_;
}
else
{
lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1505_; 
v_snd_1464_ = lean_ctor_get(v_b_1456_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_b_1456_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_b_1456_, 0);
lean_dec(v_unused_1506_);
v___x_1466_ = v_b_1456_;
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_b_1456_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1468_ = lean_array_uget_borrowed(v_as_1453_, v_i_1455_);
lean_inc(v_a_1468_);
v___x_1469_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1451_, v_a_1468_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v_a_1473_; uint8_t v___x_1480_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = lean_box(0);
v___x_1480_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1470_);
if (v___x_1480_ == 0)
{
lean_dec(v_a_1470_);
v_a_1473_ = v_snd_1464_;
goto v___jp_1472_;
}
else
{
lean_object* v_type_1481_; lean_object* v___x_1482_; 
v_type_1481_ = lean_ctor_get(v___x_1452_, 2);
lean_inc(v_a_1470_);
lean_inc_ref(v_type_1481_);
v___x_1482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1481_, v_a_1470_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; uint8_t v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = lean_unbox(v_a_1483_);
lean_dec(v_a_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_a_1470_);
v_a_1473_ = v_snd_1464_;
goto v___jp_1472_;
}
else
{
lean_object* v_self_1485_; lean_object* v___x_1486_; 
v_self_1485_ = lean_ctor_get(v_a_1470_, 0);
lean_inc_ref(v_self_1485_);
lean_dec(v_a_1470_);
v___x_1486_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1452_, v_self_1485_);
if (lean_obj_tag(v___x_1486_) == 1)
{
lean_object* v_val_1487_; lean_object* v___x_1488_; 
v_val_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1451_, v_self_1485_, v_val_1487_, v_snd_1464_);
v_a_1473_ = v___x_1488_;
goto v___jp_1472_;
}
else
{
lean_dec(v___x_1486_);
lean_dec_ref(v_self_1485_);
v_a_1473_ = v_snd_1464_;
goto v___jp_1472_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1470_);
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec_ref(v___x_1452_);
v_a_1489_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1482_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1482_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
v___jp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v_a_1473_);
lean_ctor_set(v___x_1466_, 0, v___x_1471_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1473_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
size_t v___x_1476_; size_t v___x_1477_; 
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1455_, v___x_1476_);
v_i_1455_ = v___x_1477_;
v_b_1456_ = v___x_1475_;
goto _start;
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
lean_dec_ref(v___x_1452_);
v_a_1497_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1469_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1469_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1507_, lean_object* v___x_1508_, lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_sz_boxed_1518_; size_t v_i_boxed_1519_; lean_object* v_res_1520_; 
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1519_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1507_, v___x_1508_, v_as_1509_, v_sz_boxed_1518_, v_i_boxed_1519_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_as_1509_);
lean_dec_ref(v_goal_1507_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1521_, lean_object* v___x_1522_, lean_object* v_as_1523_, size_t v_sz_1524_, size_t v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_lt(v_i_1525_, v_sz_1524_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref(v___x_1522_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_b_1526_);
return v___x_1533_;
}
else
{
lean_object* v_snd_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1575_; 
v_snd_1534_ = lean_ctor_get(v_b_1526_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_b_1526_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_b_1526_, 0);
lean_dec(v_unused_1576_);
v___x_1536_ = v_b_1526_;
v_isShared_1537_ = v_isSharedCheck_1575_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_snd_1534_);
lean_dec(v_b_1526_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1575_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_a_1538_; lean_object* v___x_1539_; 
v_a_1538_ = lean_array_uget_borrowed(v_as_1523_, v_i_1525_);
lean_inc(v_a_1538_);
v___x_1539_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1521_, v_a_1538_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; lean_object* v_a_1543_; uint8_t v___x_1550_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = lean_box(0);
v___x_1550_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1540_);
if (v___x_1550_ == 0)
{
lean_dec(v_a_1540_);
v_a_1543_ = v_snd_1534_;
goto v___jp_1542_;
}
else
{
lean_object* v_type_1551_; lean_object* v___x_1552_; 
v_type_1551_ = lean_ctor_get(v___x_1522_, 2);
lean_inc(v_a_1540_);
lean_inc_ref(v_type_1551_);
v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1551_, v_a_1540_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; uint8_t v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = lean_unbox(v_a_1553_);
lean_dec(v_a_1553_);
if (v___x_1554_ == 0)
{
lean_dec(v_a_1540_);
v_a_1543_ = v_snd_1534_;
goto v___jp_1542_;
}
else
{
lean_object* v_self_1555_; lean_object* v___x_1556_; 
v_self_1555_ = lean_ctor_get(v_a_1540_, 0);
lean_inc_ref(v_self_1555_);
lean_dec(v_a_1540_);
v___x_1556_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1522_, v_self_1555_);
if (lean_obj_tag(v___x_1556_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1558_; 
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1521_, v_self_1555_, v_val_1557_, v_snd_1534_);
v_a_1543_ = v___x_1558_;
goto v___jp_1542_;
}
else
{
lean_dec(v___x_1556_);
lean_dec_ref(v_self_1555_);
v_a_1543_ = v_snd_1534_;
goto v___jp_1542_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1540_);
lean_del_object(v___x_1536_);
lean_dec(v_snd_1534_);
lean_dec_ref(v___x_1522_);
v_a_1559_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1552_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1552_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
v___jp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v_a_1543_);
lean_ctor_set(v___x_1536_, 0, v___x_1541_);
v___x_1545_ = v___x_1536_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_a_1543_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1525_, v___x_1546_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1521_, v___x_1522_, v_as_1523_, v_sz_1524_, v___x_1547_, v___x_1545_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1536_);
lean_dec(v_snd_1534_);
lean_dec_ref(v___x_1522_);
v_a_1567_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1539_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1539_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1577_, lean_object* v___x_1578_, lean_object* v_as_1579_, lean_object* v_sz_1580_, lean_object* v_i_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1580_);
lean_dec(v_sz_1580_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1581_);
lean_dec(v_i_1581_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1577_, v___x_1578_, v_as_1579_, v_sz_boxed_1588_, v_i_boxed_1589_, v_b_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v_as_1579_);
lean_dec_ref(v_goal_1577_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1591_, lean_object* v___x_1592_, lean_object* v_t_1593_, lean_object* v_init_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_root_1600_; lean_object* v_tail_1601_; lean_object* v___x_1602_; 
v_root_1600_ = lean_ctor_get(v_t_1593_, 0);
v_tail_1601_ = lean_ctor_get(v_t_1593_, 1);
lean_inc_ref(v___x_1592_);
lean_inc_ref(v_init_1594_);
v___x_1602_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1594_, v_goal_1591_, v___x_1592_, v_root_1600_, v_init_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec_ref(v_init_1594_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1639_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1639_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1639_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
if (lean_obj_tag(v_a_1603_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; 
lean_dec_ref(v___x_1592_);
v_a_1607_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v_a_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_a_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; size_t v_sz_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
lean_del_object(v___x_1605_);
v_a_1611_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v_a_1603_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_a_1611_);
v_sz_1614_ = lean_array_size(v_tail_1601_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1591_, v___x_1592_, v_tail_1601_, v_sz_1614_, v___x_1615_, v___x_1613_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1630_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1630_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1630_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_fst_1621_; 
v_fst_1621_ = lean_ctor_get(v_a_1617_, 0);
if (lean_obj_tag(v_fst_1621_) == 0)
{
lean_object* v_snd_1622_; lean_object* v___x_1624_; 
v_snd_1622_ = lean_ctor_get(v_a_1617_, 1);
lean_inc(v_snd_1622_);
lean_dec(v_a_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_snd_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_snd_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1628_; 
lean_inc_ref(v_fst_1621_);
lean_dec(v_a_1617_);
v_val_1626_ = lean_ctor_get(v_fst_1621_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v_fst_1621_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_val_1626_);
v___x_1628_ = v___x_1619_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_val_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1616_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1616_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___x_1592_);
v_a_1640_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1602_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1602_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1648_, lean_object* v___x_1649_, lean_object* v_t_1650_, lean_object* v_init_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1648_, v___x_1649_, v_t_1650_, v_init_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_t_1650_);
lean_dec_ref(v_goal_1648_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1658_, lean_object* v_as_1659_, size_t v_sz_1660_, size_t v_i_1661_, lean_object* v_b_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_usize_dec_lt(v_i_1661_, v_sz_1660_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1662_);
return v___x_1669_;
}
else
{
lean_object* v_snd_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1701_; 
v_snd_1670_ = lean_ctor_get(v_b_1662_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_b_1662_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v_b_1662_, 0);
lean_dec(v_unused_1702_);
v___x_1672_ = v_b_1662_;
v_isShared_1673_ = v_isSharedCheck_1701_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_snd_1670_);
lean_dec(v_b_1662_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1701_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_array_uget_borrowed(v_as_1659_, v_i_1661_);
lean_inc(v_a_1674_);
v___x_1675_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1658_, v_a_1674_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v_self_1677_; lean_object* v___x_1678_; lean_object* v_a_1680_; lean_object* v___x_1687_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
v_self_1677_ = lean_ctor_get(v_a_1676_, 0);
lean_inc_ref_n(v_self_1677_, 2);
lean_dec(v_a_1676_);
v___x_1678_ = lean_box(0);
v___x_1687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1677_);
if (lean_obj_tag(v___x_1687_) == 1)
{
lean_object* v_val_1688_; lean_object* v___x_1689_; 
v_val_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1688_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1670_, v_val_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1670_, v_self_1677_);
lean_dec_ref(v_self_1677_);
if (lean_obj_tag(v___x_1690_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1692_; 
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1658_, v_val_1688_, v_val_1691_, v_snd_1670_);
v_a_1680_ = v___x_1692_;
goto v___jp_1679_;
}
else
{
lean_dec(v___x_1690_);
lean_dec(v_val_1688_);
v_a_1680_ = v_snd_1670_;
goto v___jp_1679_;
}
}
else
{
lean_dec_ref(v___x_1689_);
lean_dec(v_val_1688_);
lean_dec_ref(v_self_1677_);
v_a_1680_ = v_snd_1670_;
goto v___jp_1679_;
}
}
else
{
lean_dec(v___x_1687_);
lean_dec_ref(v_self_1677_);
v_a_1680_ = v_snd_1670_;
goto v___jp_1679_;
}
v___jp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v_a_1680_);
lean_ctor_set(v___x_1672_, 0, v___x_1678_);
v___x_1682_ = v___x_1672_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1680_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
size_t v___x_1683_; size_t v___x_1684_; 
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1661_, v___x_1683_);
v_i_1661_ = v___x_1684_;
v_b_1662_ = v___x_1682_;
goto _start;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1672_);
lean_dec(v_snd_1670_);
v_a_1693_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1675_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1675_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1703_, lean_object* v_as_1704_, lean_object* v_sz_1705_, lean_object* v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
size_t v_sz_boxed_1713_; size_t v_i_boxed_1714_; lean_object* v_res_1715_; 
v_sz_boxed_1713_ = lean_unbox_usize(v_sz_1705_);
lean_dec(v_sz_1705_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1703_, v_as_1704_, v_sz_boxed_1713_, v_i_boxed_1714_, v_b_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v_as_1704_);
lean_dec_ref(v_goal_1703_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1716_, lean_object* v_as_1717_, size_t v_sz_1718_, size_t v_i_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1719_, v_sz_1718_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_b_1720_);
return v___x_1727_;
}
else
{
lean_object* v_snd_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1759_; 
v_snd_1728_ = lean_ctor_get(v_b_1720_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_b_1720_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_b_1720_, 0);
lean_dec(v_unused_1760_);
v___x_1730_ = v_b_1720_;
v_isShared_1731_ = v_isSharedCheck_1759_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snd_1728_);
lean_dec(v_b_1720_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1759_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_a_1732_; lean_object* v___x_1733_; 
v_a_1732_ = lean_array_uget_borrowed(v_as_1717_, v_i_1719_);
lean_inc(v_a_1732_);
v___x_1733_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1716_, v_a_1732_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v_self_1735_; lean_object* v___x_1736_; lean_object* v_a_1738_; lean_object* v___x_1745_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref(v___x_1733_);
v_self_1735_ = lean_ctor_get(v_a_1734_, 0);
lean_inc_ref_n(v_self_1735_, 2);
lean_dec(v_a_1734_);
v___x_1736_ = lean_box(0);
v___x_1745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1735_);
if (lean_obj_tag(v___x_1745_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1747_; 
v_val_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_val_1746_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1728_, v_val_1746_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1728_, v_self_1735_);
lean_dec_ref(v_self_1735_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v___x_1750_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_val_1749_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1716_, v_val_1746_, v_val_1749_, v_snd_1728_);
v_a_1738_ = v___x_1750_;
goto v___jp_1737_;
}
else
{
lean_dec(v___x_1748_);
lean_dec(v_val_1746_);
v_a_1738_ = v_snd_1728_;
goto v___jp_1737_;
}
}
else
{
lean_dec_ref(v___x_1747_);
lean_dec(v_val_1746_);
lean_dec_ref(v_self_1735_);
v_a_1738_ = v_snd_1728_;
goto v___jp_1737_;
}
}
else
{
lean_dec(v___x_1745_);
lean_dec_ref(v_self_1735_);
v_a_1738_ = v_snd_1728_;
goto v___jp_1737_;
}
v___jp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v_a_1738_);
lean_ctor_set(v___x_1730_, 0, v___x_1736_);
v___x_1740_ = v___x_1730_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1738_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1719_, v___x_1741_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1716_, v_as_1717_, v_sz_1718_, v___x_1742_, v___x_1740_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1743_;
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_del_object(v___x_1730_);
lean_dec(v_snd_1728_);
v_a_1751_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1733_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1733_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1761_, lean_object* v_as_1762_, lean_object* v_sz_1763_, lean_object* v_i_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; lean_object* v_res_1773_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1761_, v_as_1762_, v_sz_boxed_1771_, v_i_boxed_1772_, v_b_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec_ref(v_as_1762_);
lean_dec_ref(v_goal_1761_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1774_, lean_object* v_as_1775_, size_t v_sz_1776_, size_t v_i_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_usize_dec_lt(v_i_1777_, v_sz_1776_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_b_1778_);
return v___x_1785_;
}
else
{
lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1817_; 
v_snd_1786_ = lean_ctor_get(v_b_1778_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_b_1778_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_b_1778_, 0);
lean_dec(v_unused_1818_);
v___x_1788_ = v_b_1778_;
v_isShared_1789_ = v_isSharedCheck_1817_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_dec(v_b_1778_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1817_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1790_ = lean_array_uget_borrowed(v_as_1775_, v_i_1777_);
lean_inc(v_a_1790_);
v___x_1791_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1774_, v_a_1790_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v_self_1793_; lean_object* v___x_1794_; lean_object* v_a_1796_; lean_object* v___x_1803_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v_self_1793_ = lean_ctor_get(v_a_1792_, 0);
lean_inc_ref_n(v_self_1793_, 2);
lean_dec(v_a_1792_);
v___x_1794_ = lean_box(0);
v___x_1803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1793_);
if (lean_obj_tag(v___x_1803_) == 1)
{
lean_object* v_val_1804_; lean_object* v___x_1805_; 
v_val_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_val_1804_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1786_, v_val_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1786_, v_self_1793_);
lean_dec_ref(v_self_1793_);
if (lean_obj_tag(v___x_1806_) == 1)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; 
v_val_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1807_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1774_, v_val_1804_, v_val_1807_, v_snd_1786_);
v_a_1796_ = v___x_1808_;
goto v___jp_1795_;
}
else
{
lean_dec(v___x_1806_);
lean_dec(v_val_1804_);
v_a_1796_ = v_snd_1786_;
goto v___jp_1795_;
}
}
else
{
lean_dec_ref(v___x_1805_);
lean_dec(v_val_1804_);
lean_dec_ref(v_self_1793_);
v_a_1796_ = v_snd_1786_;
goto v___jp_1795_;
}
}
else
{
lean_dec(v___x_1803_);
lean_dec_ref(v_self_1793_);
v_a_1796_ = v_snd_1786_;
goto v___jp_1795_;
}
v___jp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v_a_1796_);
lean_ctor_set(v___x_1788_, 0, v___x_1794_);
v___x_1798_ = v___x_1788_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1796_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1777_, v___x_1799_);
v_i_1777_ = v___x_1800_;
v_b_1778_ = v___x_1798_;
goto _start;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_del_object(v___x_1788_);
lean_dec(v_snd_1786_);
v_a_1809_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1791_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1791_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1819_, lean_object* v_as_1820_, lean_object* v_sz_1821_, lean_object* v_i_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
size_t v_sz_boxed_1829_; size_t v_i_boxed_1830_; lean_object* v_res_1831_; 
v_sz_boxed_1829_ = lean_unbox_usize(v_sz_1821_);
lean_dec(v_sz_1821_);
v_i_boxed_1830_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1819_, v_as_1820_, v_sz_boxed_1829_, v_i_boxed_1830_, v_b_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_as_1820_);
lean_dec_ref(v_goal_1819_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1832_, lean_object* v_as_1833_, size_t v_sz_1834_, size_t v_i_1835_, lean_object* v_b_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1835_, v_sz_1834_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1836_);
return v___x_1843_;
}
else
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1875_; 
v_snd_1844_ = lean_ctor_get(v_b_1836_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_b_1836_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_b_1836_, 0);
lean_dec(v_unused_1876_);
v___x_1846_ = v_b_1836_;
v_isShared_1847_ = v_isSharedCheck_1875_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v_b_1836_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1875_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_array_uget_borrowed(v_as_1833_, v_i_1835_);
lean_inc(v_a_1848_);
v___x_1849_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1832_, v_a_1848_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v_self_1851_; lean_object* v___x_1852_; lean_object* v_a_1854_; lean_object* v___x_1861_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v_self_1851_ = lean_ctor_get(v_a_1850_, 0);
lean_inc_ref_n(v_self_1851_, 2);
lean_dec(v_a_1850_);
v___x_1852_ = lean_box(0);
v___x_1861_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1851_);
if (lean_obj_tag(v___x_1861_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; 
v_val_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1844_, v_val_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1844_, v_self_1851_);
lean_dec_ref(v_self_1851_);
if (lean_obj_tag(v___x_1864_) == 1)
{
lean_object* v_val_1865_; lean_object* v___x_1866_; 
v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_val_1865_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1832_, v_val_1862_, v_val_1865_, v_snd_1844_);
v_a_1854_ = v___x_1866_;
goto v___jp_1853_;
}
else
{
lean_dec(v___x_1864_);
lean_dec(v_val_1862_);
v_a_1854_ = v_snd_1844_;
goto v___jp_1853_;
}
}
else
{
lean_dec_ref(v___x_1863_);
lean_dec(v_val_1862_);
lean_dec_ref(v_self_1851_);
v_a_1854_ = v_snd_1844_;
goto v___jp_1853_;
}
}
else
{
lean_dec(v___x_1861_);
lean_dec_ref(v_self_1851_);
v_a_1854_ = v_snd_1844_;
goto v___jp_1853_;
}
v___jp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v_a_1854_);
lean_ctor_set(v___x_1846_, 0, v___x_1852_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_a_1854_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((size_t)1ULL);
v___x_1858_ = lean_usize_add(v_i_1835_, v___x_1857_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1832_, v_as_1833_, v_sz_1834_, v___x_1858_, v___x_1856_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_del_object(v___x_1846_);
lean_dec(v_snd_1844_);
v_a_1867_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1849_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1849_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1877_, lean_object* v_as_1878_, lean_object* v_sz_1879_, lean_object* v_i_1880_, lean_object* v_b_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
size_t v_sz_boxed_1887_; size_t v_i_boxed_1888_; lean_object* v_res_1889_; 
v_sz_boxed_1887_ = lean_unbox_usize(v_sz_1879_);
lean_dec(v_sz_1879_);
v_i_boxed_1888_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_res_1889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1877_, v_as_1878_, v_sz_boxed_1887_, v_i_boxed_1888_, v_b_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v_as_1878_);
lean_dec_ref(v_goal_1877_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1890_, lean_object* v_goal_1891_, lean_object* v_n_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
if (lean_obj_tag(v_n_1892_) == 0)
{
lean_object* v_cs_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; size_t v_sz_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v_cs_1899_ = lean_ctor_get(v_n_1892_, 0);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_b_1893_);
v_sz_1902_ = lean_array_size(v_cs_1899_);
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1890_, v_goal_1891_, v_cs_1899_, v_sz_1902_, v___x_1903_, v___x_1901_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1919_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1919_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1919_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_fst_1909_; 
v_fst_1909_ = lean_ctor_get(v_a_1905_, 0);
if (lean_obj_tag(v_fst_1909_) == 0)
{
lean_object* v_snd_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v_snd_1910_ = lean_ctor_get(v_a_1905_, 1);
lean_inc(v_snd_1910_);
lean_dec(v_a_1905_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_snd_1910_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v_val_1915_; lean_object* v___x_1917_; 
lean_inc_ref(v_fst_1909_);
lean_dec(v_a_1905_);
v_val_1915_ = lean_ctor_get(v_fst_1909_, 0);
lean_inc(v_val_1915_);
lean_dec_ref(v_fst_1909_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_val_1915_);
v___x_1917_ = v___x_1907_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_val_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1904_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1904_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_vs_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; size_t v_sz_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v_vs_1928_ = lean_ctor_get(v_n_1892_, 0);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_b_1893_);
v_sz_1931_ = lean_array_size(v_vs_1928_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1891_, v_vs_1928_, v_sz_1931_, v___x_1932_, v___x_1930_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1948_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_fst_1938_; 
v_fst_1938_ = lean_ctor_get(v_a_1934_, 0);
if (lean_obj_tag(v_fst_1938_) == 0)
{
lean_object* v_snd_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v_snd_1939_ = lean_ctor_get(v_a_1934_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_a_1934_);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_snd_1939_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1940_);
v___x_1942_ = v___x_1936_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
else
{
lean_object* v_val_1944_; lean_object* v___x_1946_; 
lean_inc_ref(v_fst_1938_);
lean_dec(v_a_1934_);
v_val_1944_ = lean_ctor_get(v_fst_1938_, 0);
lean_inc(v_val_1944_);
lean_dec_ref(v_fst_1938_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_val_1944_);
v___x_1946_ = v___x_1936_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_val_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1933_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1933_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1957_, lean_object* v_goal_1958_, lean_object* v_as_1959_, size_t v_sz_1960_, size_t v_i_1961_, lean_object* v_b_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_usize_dec_lt(v_i_1961_, v_sz_1960_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_b_1962_);
return v___x_1969_;
}
else
{
lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2004_; 
v_snd_1970_ = lean_ctor_get(v_b_1962_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_b_1962_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v_b_1962_, 0);
lean_dec(v_unused_2005_);
v___x_1972_ = v_b_1962_;
v_isShared_1973_ = v_isSharedCheck_2004_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_dec(v_b_1962_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2004_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_array_uget_borrowed(v_as_1959_, v_i_1961_);
lean_inc(v_snd_1970_);
v___x_1975_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1957_, v_goal_1958_, v_a_1974_, v_snd_1970_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1995_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1995_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1995_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
if (lean_obj_tag(v_a_1976_) == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1976_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1980_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_snd_1970_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1982_);
v___x_1984_ = v___x_1978_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_del_object(v___x_1978_);
lean_dec(v_snd_1970_);
v_a_1987_ = lean_ctor_get(v_a_1976_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v_a_1976_);
v___x_1988_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v_a_1987_);
lean_ctor_set(v___x_1972_, 0, v___x_1988_);
v___x_1990_ = v___x_1972_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1987_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
size_t v___x_1991_; size_t v___x_1992_; 
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_i_1961_, v___x_1991_);
v_i_1961_ = v___x_1992_;
v_b_1962_ = v___x_1990_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_del_object(v___x_1972_);
lean_dec(v_snd_1970_);
v_a_1996_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1975_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1975_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2006_, lean_object* v_goal_2007_, lean_object* v_as_2008_, lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
size_t v_sz_boxed_2017_; size_t v_i_boxed_2018_; lean_object* v_res_2019_; 
v_sz_boxed_2017_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2006_, v_goal_2007_, v_as_2008_, v_sz_boxed_2017_, v_i_boxed_2018_, v_b_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v_as_2008_);
lean_dec_ref(v_goal_2007_);
lean_dec_ref(v_init_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2020_, lean_object* v_goal_2021_, lean_object* v_n_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2020_, v_goal_2021_, v_n_2022_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_n_2022_);
lean_dec_ref(v_goal_2021_);
lean_dec_ref(v_init_2020_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2030_, lean_object* v_t_2031_, lean_object* v_init_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_root_2038_; lean_object* v_tail_2039_; lean_object* v___x_2040_; 
v_root_2038_ = lean_ctor_get(v_t_2031_, 0);
v_tail_2039_ = lean_ctor_get(v_t_2031_, 1);
lean_inc_ref(v_init_2032_);
v___x_2040_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2032_, v_goal_2030_, v_root_2038_, v_init_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec_ref(v_init_2032_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2077_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2077_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2077_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; 
v_a_2045_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v_a_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v_a_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v_sz_2052_; size_t v___x_2053_; lean_object* v___x_2054_; 
lean_del_object(v___x_2043_);
v_a_2049_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v_a_2041_);
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_a_2049_);
v_sz_2052_ = lean_array_size(v_tail_2039_);
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2030_, v_tail_2039_, v_sz_2052_, v___x_2053_, v___x_2051_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2068_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2068_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2068_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; 
v_fst_2059_ = lean_ctor_get(v_a_2055_, 0);
if (lean_obj_tag(v_fst_2059_) == 0)
{
lean_object* v_snd_2060_; lean_object* v___x_2062_; 
v_snd_2060_ = lean_ctor_get(v_a_2055_, 1);
lean_inc(v_snd_2060_);
lean_dec(v_a_2055_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_snd_2060_);
v___x_2062_ = v___x_2057_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_snd_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v_val_2064_; lean_object* v___x_2066_; 
lean_inc_ref(v_fst_2059_);
lean_dec(v_a_2055_);
v_val_2064_ = lean_ctor_get(v_fst_2059_, 0);
lean_inc(v_val_2064_);
lean_dec_ref(v_fst_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_val_2064_);
v___x_2066_ = v___x_2057_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_val_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2054_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2054_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2040_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2040_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2086_, lean_object* v_t_2087_, lean_object* v_init_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2086_, v_t_2087_, v_init_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec_ref(v_t_2087_);
lean_dec_ref(v_goal_2086_);
return v_res_2094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_unsigned_to_nat(16u);
v___x_2097_ = lean_mk_array(v___x_2096_, v___x_2095_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_model_2100_; 
v___x_2098_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2099_ = lean_unsigned_to_nat(0u);
v_model_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2100_, 0, v___x_2099_);
lean_ctor_set(v_model_2100_, 1, v___x_2098_);
return v_model_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2108_, lean_object* v_structId_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2116_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2115_, v_goal_2108_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_toGoalState_2118_; lean_object* v_structs_2119_; lean_object* v_exprs_2120_; lean_object* v___x_2121_; lean_object* v_model_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2116_);
v_toGoalState_2118_ = lean_ctor_get(v_goal_2108_, 0);
v_structs_2119_ = lean_ctor_get(v_a_2117_, 0);
lean_inc_ref(v_structs_2119_);
lean_dec(v_a_2117_);
v_exprs_2120_ = lean_ctor_get(v_toGoalState_2118_, 2);
v___x_2121_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2122_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2123_ = lean_array_get(v___x_2121_, v_structs_2119_, v_structId_2109_);
lean_dec_ref(v_structs_2119_);
lean_inc(v___x_2123_);
v___x_2124_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2108_, v___x_2123_, v_exprs_2120_, v_model_2122_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2108_, v_structId_2109_, v_a_2125_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2108_, v_exprs_2120_, v_a_2127_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v_type_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
v_type_2130_ = lean_ctor_get(v___x_2123_, 2);
lean_inc_ref(v_type_2130_);
lean_dec(v___x_2123_);
v___x_2131_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2131_, 0, v_type_2130_);
v___x_2132_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2108_, v___x_2131_, v_a_2129_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2135_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2134_, v_a_2133_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2135_, 0);
lean_dec(v_unused_2143_);
v___x_2137_ = v___x_2135_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v___x_2135_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_a_2133_);
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2133_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2133_);
v_a_2144_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2135_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2135_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
return v___x_2132_;
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v___x_2123_);
v_a_2152_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2128_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2128_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v___x_2123_);
v_a_2160_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2126_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2126_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v___x_2123_);
v_a_2168_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2124_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2124_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2188_; 
v_a_2176_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2178_ = v___x_2116_;
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2116_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_ref_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v_ref_2180_ = lean_ctor_get(v_a_2112_, 5);
v___x_2181_ = lean_io_error_to_string(v_a_2176_);
v___x_2182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
v___x_2183_ = l_Lean_MessageData_ofFormat(v___x_2182_);
lean_inc(v_ref_2180_);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_ref_2180_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2184_);
v___x_2186_ = v___x_2178_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2189_, lean_object* v_structId_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2189_, v_structId_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_structId_2190_);
lean_dec_ref(v_goal_2189_);
return v_res_2196_;
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

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.ModelUtil
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Model"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Model.0.Lean.Meta.Grind.Arith.Cutsat.getCutsatAssignment\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: isSameExpr node.self node.root\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 249, 151, 171, 150, 156, 160, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 153, 248, 110, 186, 235, 101, 152)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0(void){
_start:
{
uint8_t v___x_1_; uint64_t v___x_2_; 
v___x_1_ = 1;
v___x_2_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object* v_n_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_self_9_; lean_object* v___x_10_; uint8_t v_foApprox_11_; uint8_t v_ctxApprox_12_; uint8_t v_quasiPatternApprox_13_; uint8_t v_constApprox_14_; uint8_t v_isDefEqStuckEx_15_; uint8_t v_unificationHints_16_; uint8_t v_proofIrrelevance_17_; uint8_t v_assignSyntheticOpaque_18_; uint8_t v_offsetCnstrs_19_; uint8_t v_etaStruct_20_; uint8_t v_univApprox_21_; uint8_t v_iota_22_; uint8_t v_beta_23_; uint8_t v_proj_24_; uint8_t v_zeta_25_; uint8_t v_zetaDelta_26_; uint8_t v_zetaUnused_27_; uint8_t v_zetaHave_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_83_; 
v_self_9_ = lean_ctor_get(v_n_3_, 0);
lean_inc_ref(v_self_9_);
lean_dec_ref(v_n_3_);
v___x_10_ = l_Lean_Meta_Context_config(v_a_4_);
v_foApprox_11_ = lean_ctor_get_uint8(v___x_10_, 0);
v_ctxApprox_12_ = lean_ctor_get_uint8(v___x_10_, 1);
v_quasiPatternApprox_13_ = lean_ctor_get_uint8(v___x_10_, 2);
v_constApprox_14_ = lean_ctor_get_uint8(v___x_10_, 3);
v_isDefEqStuckEx_15_ = lean_ctor_get_uint8(v___x_10_, 4);
v_unificationHints_16_ = lean_ctor_get_uint8(v___x_10_, 5);
v_proofIrrelevance_17_ = lean_ctor_get_uint8(v___x_10_, 6);
v_assignSyntheticOpaque_18_ = lean_ctor_get_uint8(v___x_10_, 7);
v_offsetCnstrs_19_ = lean_ctor_get_uint8(v___x_10_, 8);
v_etaStruct_20_ = lean_ctor_get_uint8(v___x_10_, 10);
v_univApprox_21_ = lean_ctor_get_uint8(v___x_10_, 11);
v_iota_22_ = lean_ctor_get_uint8(v___x_10_, 12);
v_beta_23_ = lean_ctor_get_uint8(v___x_10_, 13);
v_proj_24_ = lean_ctor_get_uint8(v___x_10_, 14);
v_zeta_25_ = lean_ctor_get_uint8(v___x_10_, 15);
v_zetaDelta_26_ = lean_ctor_get_uint8(v___x_10_, 16);
v_zetaUnused_27_ = lean_ctor_get_uint8(v___x_10_, 17);
v_zetaHave_28_ = lean_ctor_get_uint8(v___x_10_, 18);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_83_ == 0)
{
v___x_30_ = v___x_10_;
v_isShared_31_ = v_isSharedCheck_83_;
goto v_resetjp_29_;
}
else
{
lean_dec(v___x_10_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_83_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v_trackZetaDelta_32_; lean_object* v_zetaDeltaSet_33_; lean_object* v_lctx_34_; lean_object* v_localInstances_35_; lean_object* v_defEqCtx_x3f_36_; lean_object* v_synthPendingDepth_37_; lean_object* v_canUnfold_x3f_38_; uint8_t v_univApprox_39_; uint8_t v_inTypeClassResolution_40_; uint8_t v_cacheInferType_41_; uint8_t v___x_42_; lean_object* v_config_44_; 
v_trackZetaDelta_32_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7);
v_zetaDeltaSet_33_ = lean_ctor_get(v_a_4_, 1);
lean_inc(v_zetaDeltaSet_33_);
v_lctx_34_ = lean_ctor_get(v_a_4_, 2);
lean_inc_ref(v_lctx_34_);
v_localInstances_35_ = lean_ctor_get(v_a_4_, 3);
lean_inc_ref(v_localInstances_35_);
v_defEqCtx_x3f_36_ = lean_ctor_get(v_a_4_, 4);
lean_inc(v_defEqCtx_x3f_36_);
v_synthPendingDepth_37_ = lean_ctor_get(v_a_4_, 5);
lean_inc(v_synthPendingDepth_37_);
v_canUnfold_x3f_38_ = lean_ctor_get(v_a_4_, 6);
lean_inc(v_canUnfold_x3f_38_);
v_univApprox_39_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_40_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 2);
v_cacheInferType_41_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 3);
v___x_42_ = 1;
if (v_isShared_31_ == 0)
{
v_config_44_ = v___x_30_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 0, v_foApprox_11_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 1, v_ctxApprox_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 2, v_quasiPatternApprox_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 3, v_constApprox_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 4, v_isDefEqStuckEx_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 5, v_unificationHints_16_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 6, v_proofIrrelevance_17_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 7, v_assignSyntheticOpaque_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 8, v_offsetCnstrs_19_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 10, v_etaStruct_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 11, v_univApprox_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 12, v_iota_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 13, v_beta_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 14, v_proj_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 15, v_zeta_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 16, v_zetaDelta_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 17, v_zetaUnused_27_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, 18, v_zetaHave_28_);
v_config_44_ = v_reuseFailAlloc_82_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
uint64_t v___x_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_74_; 
lean_ctor_set_uint8(v_config_44_, 9, v___x_42_);
v___x_45_ = l_Lean_Meta_Context_configKey(v_a_4_);
v_isSharedCheck_74_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_74_ == 0)
{
lean_object* v_unused_75_; lean_object* v_unused_76_; lean_object* v_unused_77_; lean_object* v_unused_78_; lean_object* v_unused_79_; lean_object* v_unused_80_; lean_object* v_unused_81_; 
v_unused_75_ = lean_ctor_get(v_a_4_, 6);
lean_dec(v_unused_75_);
v_unused_76_ = lean_ctor_get(v_a_4_, 5);
lean_dec(v_unused_76_);
v_unused_77_ = lean_ctor_get(v_a_4_, 4);
lean_dec(v_unused_77_);
v_unused_78_ = lean_ctor_get(v_a_4_, 3);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_a_4_, 2);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v_a_4_, 1);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_a_4_, 0);
lean_dec(v_unused_81_);
v___x_47_ = v_a_4_;
v_isShared_48_ = v_isSharedCheck_74_;
goto v_resetjp_46_;
}
else
{
lean_dec(v_a_4_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_74_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v_key_53_; lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_49_ = 2ULL;
v___x_50_ = lean_uint64_shift_right(v___x_45_, v___x_49_);
v___x_51_ = lean_uint64_shift_left(v___x_50_, v___x_49_);
v___x_52_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0);
v_key_53_ = lean_uint64_lor(v___x_51_, v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_54_, 0, v_config_44_);
lean_ctor_set_uint64(v___x_54_, sizeof(void*)*1, v_key_53_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_54_);
v___x_56_ = v___x_47_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_zetaDeltaSet_33_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_lctx_34_);
lean_ctor_set(v_reuseFailAlloc_73_, 3, v_localInstances_35_);
lean_ctor_set(v_reuseFailAlloc_73_, 4, v_defEqCtx_x3f_36_);
lean_ctor_set(v_reuseFailAlloc_73_, 5, v_synthPendingDepth_37_);
lean_ctor_set(v_reuseFailAlloc_73_, 6, v_canUnfold_x3f_38_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*7, v_trackZetaDelta_32_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*7 + 1, v_univApprox_39_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*7 + 2, v_inTypeClassResolution_40_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*7 + 3, v_cacheInferType_41_);
v___x_56_ = v_reuseFailAlloc_73_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; 
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v___x_56_);
v___x_57_ = lean_infer_type(v_self_9_, v___x_56_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref(v___x_57_);
v___x_59_ = l_Lean_Int_mkType;
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v___x_56_);
lean_inc(v_a_58_);
v___x_60_ = l_Lean_Meta_isExprDefEq(v_a_58_, v___x_59_, v___x_56_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; uint8_t v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v___x_62_ = lean_unbox(v_a_61_);
lean_dec(v_a_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec_ref(v___x_60_);
v___x_63_ = l_Lean_Nat_mkType;
v___x_64_ = l_Lean_Meta_isExprDefEq(v_a_58_, v___x_63_, v___x_56_, v_a_5_, v_a_6_, v_a_7_);
return v___x_64_;
}
else
{
lean_dec(v_a_58_);
lean_dec_ref(v___x_56_);
lean_dec(v_a_7_);
lean_dec_ref(v_a_6_);
lean_dec(v_a_5_);
return v___x_60_;
}
}
else
{
lean_dec(v_a_58_);
lean_dec_ref(v___x_56_);
lean_dec(v_a_7_);
lean_dec_ref(v_a_6_);
lean_dec(v_a_5_);
return v___x_60_;
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec_ref(v___x_56_);
lean_dec(v_a_7_);
lean_dec_ref(v_a_6_);
lean_dec(v_a_5_);
v_a_65_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_57_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_57_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object* v_n_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
return v_res_90_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___f_92_; 
v___x_91_ = l_instInhabitedError;
v___f_92_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object* v_msg_93_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_858__overap_96_; lean_object* v___x_97_; 
v___f_95_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_858__overap_96_ = lean_panic_fn(v___f_95_, v_msg_93_);
v___x_97_ = lean_apply_1(v___x_858__overap_96_, lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object* v_msg_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_101_, lean_object* v_vals_102_, lean_object* v_i_103_, lean_object* v_k_104_){
_start:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_array_get_size(v_keys_101_);
v___x_106_ = lean_nat_dec_lt(v_i_103_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v_i_103_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v_k_x27_108_; uint8_t v___x_109_; 
v_k_x27_108_ = lean_array_fget_borrowed(v_keys_101_, v_i_103_);
v___x_109_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_104_, v_k_x27_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_i_103_, v___x_110_);
lean_dec(v_i_103_);
v_i_103_ = v___x_111_;
goto _start;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_array_fget_borrowed(v_vals_102_, v_i_103_);
lean_dec(v_i_103_);
lean_inc(v___x_113_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_115_, lean_object* v_vals_116_, lean_object* v_i_117_, lean_object* v_k_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_115_, v_vals_116_, v_i_117_, v_k_118_);
lean_dec_ref(v_k_118_);
lean_dec_ref(v_vals_116_);
lean_dec_ref(v_keys_115_);
return v_res_119_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; 
v___x_120_ = ((size_t)5ULL);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_shift_left(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0);
v___x_125_ = lean_usize_sub(v___x_124_, v___x_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object* v_x_126_, size_t v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v_es_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_150_; 
v_es_129_ = lean_ctor_get(v_x_126_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_150_ == 0)
{
v___x_131_ = v_x_126_;
v_isShared_132_ = v_isSharedCheck_150_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_es_129_);
lean_dec(v_x_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_150_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v_j_137_; lean_object* v___x_138_; 
v___x_133_ = lean_box(2);
v___x_134_ = ((size_t)5ULL);
v___x_135_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1);
v___x_136_ = lean_usize_land(v_x_127_, v___x_135_);
v_j_137_ = lean_usize_to_nat(v___x_136_);
v___x_138_ = lean_array_get(v___x_133_, v_es_129_, v_j_137_);
lean_dec(v_j_137_);
lean_dec_ref(v_es_129_);
switch(lean_obj_tag(v___x_138_))
{
case 0:
{
lean_object* v_key_139_; lean_object* v_val_140_; uint8_t v___x_141_; 
v_key_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_key_139_);
v_val_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_val_140_);
lean_dec_ref(v___x_138_);
v___x_141_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_128_, v_key_139_);
lean_dec(v_key_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec(v_val_140_);
lean_del_object(v___x_131_);
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v___x_144_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 0, v_val_140_);
v___x_144_ = v___x_131_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_val_140_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
case 1:
{
lean_object* v_node_146_; size_t v___x_147_; 
lean_del_object(v___x_131_);
v_node_146_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_node_146_);
lean_dec_ref(v___x_138_);
v___x_147_ = lean_usize_shift_right(v_x_127_, v___x_134_);
v_x_126_ = v_node_146_;
v_x_127_ = v___x_147_;
goto _start;
}
default: 
{
lean_object* v___x_149_; 
lean_del_object(v___x_131_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
}
}
else
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_151_ = lean_ctor_get(v_x_126_, 0);
lean_inc_ref(v_ks_151_);
v_vs_152_ = lean_ctor_get(v_x_126_, 1);
lean_inc_ref(v_vs_152_);
lean_dec_ref(v_x_126_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_151_, v_vs_152_, v___x_153_, v_x_128_);
lean_dec_ref(v_vs_152_);
lean_dec_ref(v_ks_151_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
size_t v_x_1032__boxed_158_; lean_object* v_res_159_; 
v_x_1032__boxed_158_ = lean_unbox_usize(v_x_156_);
lean_dec(v_x_156_);
v_res_159_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_155_, v_x_1032__boxed_158_, v_x_157_);
lean_dec_ref(v_x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint64_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_161_);
v___x_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_160_, v___x_163_, v_x_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_165_, v_x_166_);
lean_dec_ref(v_x_166_);
return v_res_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2));
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = lean_unsigned_to_nat(21u);
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1));
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0));
v___x_176_ = l_mkPanicMessageWithDecl(v___x_175_, v___x_174_, v___x_173_, v___x_172_, v___x_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object* v_goal_177_, lean_object* v_node_178_){
_start:
{
lean_object* v_self_180_; lean_object* v_root_181_; uint8_t v___x_182_; 
v_self_180_ = lean_ctor_get(v_node_178_, 0);
v_root_181_ = lean_ctor_get(v_node_178_, 2);
v___x_182_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_180_, v_root_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_184_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_186_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_185_, v_node_178_);
if (lean_obj_tag(v___x_186_) == 1)
{
lean_object* v_val_187_; lean_object* v___x_188_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v___x_186_);
v___x_188_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_185_, v_goal_177_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_219_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_219_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_219_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_219_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_varMap_193_; lean_object* v_assignment_194_; lean_object* v___x_195_; 
v_varMap_193_ = lean_ctor_get(v_a_189_, 1);
lean_inc_ref(v_varMap_193_);
v_assignment_194_ = lean_ctor_get(v_a_189_, 13);
lean_inc_ref(v_assignment_194_);
lean_dec(v_a_189_);
v___x_195_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_193_, v_val_187_);
lean_dec(v_val_187_);
if (lean_obj_tag(v___x_195_) == 1)
{
lean_object* v_val_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_214_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_214_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_214_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_val_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_214_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_size_200_; uint8_t v___x_201_; 
v_size_200_ = lean_ctor_get(v_assignment_194_, 2);
v___x_201_ = lean_nat_dec_lt(v_val_196_, v_size_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_del_object(v___x_198_);
lean_dec(v_val_196_);
lean_dec_ref(v_assignment_194_);
v___x_202_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_202_);
v___x_204_ = v___x_191_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = l_instInhabitedRat;
v___x_207_ = l_Lean_PersistentArray_get_x21___redArg(v___x_206_, v_assignment_194_, v_val_196_);
lean_dec(v_val_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_207_);
v___x_209_ = v___x_198_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_209_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_dec(v___x_195_);
lean_dec_ref(v_assignment_194_);
v___x_215_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_215_);
v___x_217_ = v___x_191_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
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
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_val_187_);
v_a_220_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_188_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_188_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v___x_186_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_230_, lean_object* v_node_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_230_, v_node_231_);
lean_dec_ref(v_node_231_);
lean_dec_ref(v_goal_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_235_, v_x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_238_, v_x_239_, v_x_240_);
lean_dec_ref(v_x_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_242_, lean_object* v_x_243_, size_t v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_243_, v_x_244_, v_x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
size_t v_x_1237__boxed_251_; lean_object* v_res_252_; 
v_x_1237__boxed_251_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_res_252_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_247_, v_x_248_, v_x_1237__boxed_251_, v_x_250_);
lean_dec_ref(v_x_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_253_, lean_object* v_keys_254_, lean_object* v_vals_255_, lean_object* v_heq_256_, lean_object* v_i_257_, lean_object* v_k_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_254_, v_vals_255_, v_i_257_, v_k_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_260_, lean_object* v_keys_261_, lean_object* v_vals_262_, lean_object* v_heq_263_, lean_object* v_i_264_, lean_object* v_k_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_260_, v_keys_261_, v_vals_262_, v_heq_263_, v_i_264_, v_k_265_);
lean_dec_ref(v_k_265_);
lean_dec_ref(v_vals_262_);
lean_dec_ref(v_keys_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = l_Lean_Expr_cleanupAnnotations(v_e_284_);
v___x_286_ = l_Lean_Expr_isApp(v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v___x_285_);
v___x_287_ = lean_box(0);
return v___x_287_;
}
else
{
lean_object* v_arg_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_arg_288_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_arg_288_);
v___x_289_ = l_Lean_Expr_appFnCleanup___redArg(v___x_285_);
v___x_290_ = l_Lean_Expr_isApp(v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec_ref(v___x_289_);
lean_dec_ref(v_arg_288_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v_arg_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_arg_292_ = lean_ctor_get(v___x_289_, 1);
lean_inc_ref(v_arg_292_);
v___x_293_ = l_Lean_Expr_appFnCleanup___redArg(v___x_289_);
v___x_294_ = l_Lean_Expr_isApp(v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec_ref(v___x_293_);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_arg_288_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_293_);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
lean_dec_ref(v_arg_292_);
v___x_299_ = l_Lean_Expr_isApp(v___x_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_296_);
lean_dec_ref(v_arg_288_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_296_);
v___x_302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_302_);
lean_dec_ref(v___x_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec_ref(v_arg_288_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_arg_288_);
return v___x_305_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
lean_dec_ref(v___x_296_);
v___x_306_ = l_Lean_Expr_cleanupAnnotations(v_arg_292_);
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_306_, v___x_307_);
lean_dec_ref(v___x_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_arg_288_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_arg_288_);
return v___x_310_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Rat_ofInt(v_a_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_313_, lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
lean_inc_ref(v_goal_313_);
v___x_320_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_313_, v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
lean_inc_ref(v_goal_313_);
v___x_322_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_313_, v_a_321_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_322_);
v___x_324_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_313_, v_a_323_);
lean_dec_ref(v_goal_313_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_390_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_390_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_390_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_390_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
if (lean_obj_tag(v_a_325_) == 1)
{
lean_object* v___x_330_; 
lean_dec(v_a_323_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
else
{
lean_object* v_self_332_; lean_object* v___x_333_; 
lean_del_object(v___x_327_);
lean_dec(v_a_325_);
v_self_332_ = lean_ctor_get(v_a_323_, 0);
lean_inc_ref(v_self_332_);
lean_dec(v_a_323_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
lean_inc_ref(v_self_332_);
v___x_333_ = l_Lean_Meta_getIntValue_x3f(v_self_332_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_381_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_381_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_381_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_381_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v_self_332_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
v_val_338_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_349_ == 0)
{
v___x_340_ = v_a_334_;
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v_a_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = l_Rat_ofInt(v_val_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_344_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v___x_350_; 
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
v___x_350_ = l_Lean_Meta_getNatValue_x3f(v_self_332_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec_ref(v_self_332_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_372_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_372_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
if (lean_obj_tag(v_a_351_) == 1)
{
lean_object* v_val_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_367_; 
v_val_355_ = lean_ctor_get(v_a_351_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_367_ == 0)
{
v___x_357_ = v_a_351_;
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_val_355_);
lean_dec(v_a_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_nat_to_int(v_val_355_);
v___x_360_ = l_Rat_ofInt(v___x_359_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
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
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_362_);
v___x_364_ = v___x_353_;
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
else
{
lean_object* v___x_368_; lean_object* v___x_370_; 
lean_dec(v_a_351_);
v___x_368_ = lean_box(0);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_368_);
v___x_370_ = v___x_353_;
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
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_350_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_350_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v_self_332_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
v_a_382_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_333_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_333_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_a_323_);
lean_dec(v_a_318_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
v_a_391_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_403_ == 0)
{
v___x_393_ = v___x_324_;
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_324_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_ref_395_ = lean_ctor_get(v_a_317_, 5);
lean_inc(v_ref_395_);
lean_dec_ref(v_a_317_);
v___x_396_ = lean_io_error_to_string(v_a_391_);
v___x_397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = l_Lean_MessageData_ofFormat(v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_399_);
v___x_401_ = v___x_393_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_goal_313_);
v_a_404_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_322_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_322_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_goal_313_);
v_a_412_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_320_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_320_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_420_, lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_420_, v_e_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_428_, lean_object* v_as_429_, size_t v_sz_430_, size_t v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_goal_428_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_b_432_);
return v___x_439_;
}
else
{
lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_489_; 
v_snd_440_ = lean_ctor_get(v_b_432_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_b_432_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_b_432_, 0);
lean_dec(v_unused_490_);
v___x_442_ = v_b_432_;
v_isShared_443_ = v_isSharedCheck_489_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_dec(v_b_432_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_489_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_array_uget_borrowed(v_as_429_, v_i_431_);
lean_inc(v_a_444_);
lean_inc_ref(v_goal_428_);
v___x_445_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_428_, v_a_444_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_447_; lean_object* v_a_449_; uint8_t v___x_456_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v___x_447_ = lean_box(0);
v___x_456_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_446_);
if (v___x_456_ == 0)
{
lean_dec(v_a_446_);
v_a_449_ = v_snd_440_;
goto v___jp_448_;
}
else
{
lean_object* v___x_457_; 
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v_a_446_);
v___x_457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_446_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_459_ == 0)
{
lean_dec(v_a_446_);
v_a_449_ = v_snd_440_;
goto v___jp_448_;
}
else
{
lean_object* v_self_460_; lean_object* v___x_461_; 
v_self_460_ = lean_ctor_get(v_a_446_, 0);
lean_inc_ref(v_self_460_);
lean_dec(v_a_446_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc_ref(v_self_460_);
lean_inc_ref(v_goal_428_);
v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_428_, v_self_460_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref(v___x_461_);
if (lean_obj_tag(v_a_462_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_464_; 
v_val_463_ = lean_ctor_get(v_a_462_, 0);
lean_inc(v_val_463_);
lean_dec_ref(v_a_462_);
lean_inc_ref(v_goal_428_);
v___x_464_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_428_, v_self_460_, v_val_463_, v_snd_440_);
v_a_449_ = v___x_464_;
goto v___jp_448_;
}
else
{
lean_dec(v_a_462_);
lean_dec_ref(v_self_460_);
v_a_449_ = v_snd_440_;
goto v___jp_448_;
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_self_460_);
lean_del_object(v___x_442_);
lean_dec(v_snd_440_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_goal_428_);
v_a_465_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_461_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_a_446_);
lean_del_object(v___x_442_);
lean_dec(v_snd_440_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_goal_428_);
v_a_473_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_457_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_457_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
v___jp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v_a_449_);
lean_ctor_set(v___x_442_, 0, v___x_447_);
v___x_451_ = v___x_442_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_449_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
size_t v___x_452_; size_t v___x_453_; 
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_431_, v___x_452_);
v_i_431_ = v___x_453_;
v_b_432_ = v___x_451_;
goto _start;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_442_);
lean_dec(v_snd_440_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_goal_428_);
v_a_481_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_445_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_445_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_491_, lean_object* v_as_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_502_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_491_, v_as_492_, v_sz_boxed_501_, v_i_boxed_502_, v_b_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec_ref(v_as_492_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_504_, lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_goal_504_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_b_508_);
return v___x_515_;
}
else
{
lean_object* v_snd_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_565_; 
v_snd_516_ = lean_ctor_get(v_b_508_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_b_508_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_b_508_, 0);
lean_dec(v_unused_566_);
v___x_518_ = v_b_508_;
v_isShared_519_ = v_isSharedCheck_565_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snd_516_);
lean_dec(v_b_508_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_565_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
lean_inc(v_a_520_);
lean_inc_ref(v_goal_504_);
v___x_521_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_504_, v_a_520_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v_a_525_; uint8_t v___x_532_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_box(0);
v___x_532_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_522_);
if (v___x_532_ == 0)
{
lean_dec(v_a_522_);
v_a_525_ = v_snd_516_;
goto v___jp_524_;
}
else
{
lean_object* v___x_533_; 
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v_a_522_);
v___x_533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_522_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v___x_533_);
v___x_535_ = lean_unbox(v_a_534_);
lean_dec(v_a_534_);
if (v___x_535_ == 0)
{
lean_dec(v_a_522_);
v_a_525_ = v_snd_516_;
goto v___jp_524_;
}
else
{
lean_object* v_self_536_; lean_object* v___x_537_; 
v_self_536_ = lean_ctor_get(v_a_522_, 0);
lean_inc_ref(v_self_536_);
lean_dec(v_a_522_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc_ref(v_self_536_);
lean_inc_ref(v_goal_504_);
v___x_537_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_504_, v_self_536_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v___x_537_);
if (lean_obj_tag(v_a_538_) == 1)
{
lean_object* v_val_539_; lean_object* v___x_540_; 
v_val_539_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref(v_a_538_);
lean_inc_ref(v_goal_504_);
v___x_540_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_504_, v_self_536_, v_val_539_, v_snd_516_);
v_a_525_ = v___x_540_;
goto v___jp_524_;
}
else
{
lean_dec(v_a_538_);
lean_dec_ref(v_self_536_);
v_a_525_ = v_snd_516_;
goto v___jp_524_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_self_536_);
lean_del_object(v___x_518_);
lean_dec(v_snd_516_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_goal_504_);
v_a_541_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_537_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_522_);
lean_del_object(v___x_518_);
lean_dec(v_snd_516_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_goal_504_);
v_a_549_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_533_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_533_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
v___jp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v_a_525_);
lean_ctor_set(v___x_518_, 0, v___x_523_);
v___x_527_ = v___x_518_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_525_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_507_, v___x_528_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_504_, v_as_505_, v_sz_506_, v___x_529_, v___x_527_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
return v___x_530_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_del_object(v___x_518_);
lean_dec(v_snd_516_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_goal_504_);
v_a_557_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_521_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_521_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_567_, lean_object* v_as_568_, lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_b_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_578_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_567_, v_as_568_, v_sz_boxed_577_, v_i_boxed_578_, v_b_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec_ref(v_as_568_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_goal_580_, lean_object* v_inh_581_, lean_object* v_n_582_, lean_object* v_b_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_n_582_) == 0)
{
lean_object* v_cs_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_623_; 
v_cs_589_ = lean_ctor_get(v_n_582_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_n_582_);
if (v_isSharedCheck_623_ == 0)
{
v___x_591_ = v_n_582_;
v_isShared_592_ = v_isSharedCheck_623_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_cs_589_);
lean_dec(v_n_582_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_623_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; size_t v_sz_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_593_ = lean_box(0);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v_b_583_);
v_sz_595_ = lean_array_size(v_cs_589_);
v___x_596_ = ((size_t)0ULL);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_goal_580_, v_inh_581_, v_cs_589_, v_sz_595_, v___x_596_, v___x_594_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec_ref(v_cs_589_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_614_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_614_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_fst_602_; 
v_fst_602_ = lean_ctor_get(v_a_598_, 0);
if (lean_obj_tag(v_fst_602_) == 0)
{
lean_object* v_snd_603_; lean_object* v___x_605_; 
v_snd_603_ = lean_ctor_get(v_a_598_, 1);
lean_inc(v_snd_603_);
lean_dec(v_a_598_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
lean_ctor_set(v___x_591_, 0, v_snd_603_);
v___x_605_ = v___x_591_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_snd_603_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_605_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_val_610_; lean_object* v___x_612_; 
lean_inc_ref(v_fst_602_);
lean_dec(v_a_598_);
lean_del_object(v___x_591_);
v_val_610_ = lean_ctor_get(v_fst_602_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v_fst_602_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_val_610_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_val_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_del_object(v___x_591_);
v_a_615_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_597_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_597_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
else
{
lean_object* v_vs_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_658_; 
v_vs_624_ = lean_ctor_get(v_n_582_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_n_582_);
if (v_isSharedCheck_658_ == 0)
{
v___x_626_ = v_n_582_;
v_isShared_627_ = v_isSharedCheck_658_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_vs_624_);
lean_dec(v_n_582_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_658_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_b_583_);
v_sz_630_ = lean_array_size(v_vs_624_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_580_, v_vs_624_, v_sz_630_, v___x_631_, v___x_629_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec_ref(v_vs_624_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_649_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_649_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_649_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_649_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; 
v_fst_637_ = lean_ctor_get(v_a_633_, 0);
if (lean_obj_tag(v_fst_637_) == 0)
{
lean_object* v_snd_638_; lean_object* v___x_640_; 
v_snd_638_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_638_);
lean_dec(v_a_633_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v_snd_638_);
v___x_640_ = v___x_626_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_snd_638_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_640_);
v___x_642_ = v___x_635_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_val_645_; lean_object* v___x_647_; 
lean_inc_ref(v_fst_637_);
lean_dec(v_a_633_);
lean_del_object(v___x_626_);
v_val_645_ = lean_ctor_get(v_fst_637_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v_fst_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_val_645_);
v___x_647_ = v___x_635_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_del_object(v___x_626_);
v_a_650_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_632_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_632_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_goal_659_, lean_object* v_inh_660_, lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_goal_659_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_b_664_);
return v___x_671_;
}
else
{
lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_706_; 
v_snd_672_ = lean_ctor_get(v_b_664_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_b_664_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_b_664_, 0);
lean_dec(v_unused_707_);
v___x_674_ = v_b_664_;
v_isShared_675_ = v_isSharedCheck_706_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_dec(v_b_664_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_706_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v_snd_672_);
lean_inc(v_a_676_);
lean_inc_ref(v_goal_659_);
v___x_677_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_goal_659_, v_inh_660_, v_a_676_, v_snd_672_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_697_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_697_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_697_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_697_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_goal_659_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_a_678_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_682_);
v___x_684_ = v___x_674_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_snd_672_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_del_object(v___x_680_);
lean_dec(v_snd_672_);
v_a_689_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v_a_678_);
v___x_690_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_a_689_);
lean_ctor_set(v___x_674_, 0, v___x_690_);
v___x_692_ = v___x_674_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_689_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
size_t v___x_693_; size_t v___x_694_; 
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_663_, v___x_693_);
v_i_663_ = v___x_694_;
v_b_664_ = v___x_692_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_del_object(v___x_674_);
lean_dec(v_snd_672_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_goal_659_);
v_a_698_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_677_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_677_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_goal_708_, lean_object* v_inh_709_, lean_object* v_as_710_, lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
size_t v_sz_boxed_719_; size_t v_i_boxed_720_; lean_object* v_res_721_; 
v_sz_boxed_719_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_720_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_goal_708_, v_inh_709_, v_as_710_, v_sz_boxed_719_, v_i_boxed_720_, v_b_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec_ref(v_as_710_);
lean_dec_ref(v_inh_709_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_goal_722_, lean_object* v_inh_723_, lean_object* v_n_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_goal_722_, v_inh_723_, v_n_724_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec_ref(v_inh_723_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_732_, lean_object* v_as_733_, size_t v_sz_734_, size_t v_i_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_goal_732_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_b_736_);
return v___x_743_;
}
else
{
lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_793_; 
v_snd_744_ = lean_ctor_get(v_b_736_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_b_736_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_b_736_, 0);
lean_dec(v_unused_794_);
v___x_746_ = v_b_736_;
v_isShared_747_ = v_isSharedCheck_793_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_b_736_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_793_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_array_uget_borrowed(v_as_733_, v_i_735_);
lean_inc(v_a_748_);
lean_inc_ref(v_goal_732_);
v___x_749_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_732_, v_a_748_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v_a_753_; uint8_t v___x_760_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v___x_751_ = lean_box(0);
v___x_760_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_750_);
if (v___x_760_ == 0)
{
lean_dec(v_a_750_);
v_a_753_ = v_snd_744_;
goto v___jp_752_;
}
else
{
lean_object* v___x_761_; 
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v_a_750_);
v___x_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_750_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; uint8_t v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = lean_unbox(v_a_762_);
lean_dec(v_a_762_);
if (v___x_763_ == 0)
{
lean_dec(v_a_750_);
v_a_753_ = v_snd_744_;
goto v___jp_752_;
}
else
{
lean_object* v_self_764_; lean_object* v___x_765_; 
v_self_764_ = lean_ctor_get(v_a_750_, 0);
lean_inc_ref(v_self_764_);
lean_dec(v_a_750_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc_ref(v_self_764_);
lean_inc_ref(v_goal_732_);
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_732_, v_self_764_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v___x_765_);
if (lean_obj_tag(v_a_766_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v_a_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v_a_766_);
lean_inc_ref(v_goal_732_);
v___x_768_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_732_, v_self_764_, v_val_767_, v_snd_744_);
v_a_753_ = v___x_768_;
goto v___jp_752_;
}
else
{
lean_dec(v_a_766_);
lean_dec_ref(v_self_764_);
v_a_753_ = v_snd_744_;
goto v___jp_752_;
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_self_764_);
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_goal_732_);
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
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_a_750_);
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_goal_732_);
v_a_777_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_761_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_761_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
v___jp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_a_753_);
lean_ctor_set(v___x_746_, 0, v___x_751_);
v___x_755_ = v___x_746_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
size_t v___x_756_; size_t v___x_757_; 
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_735_, v___x_756_);
v_i_735_ = v___x_757_;
v_b_736_ = v___x_755_;
goto _start;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_goal_732_);
v_a_785_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_749_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_749_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_795_, lean_object* v_as_796_, lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_806_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_795_, v_as_796_, v_sz_boxed_805_, v_i_boxed_806_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec_ref(v_as_796_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_808_, lean_object* v_as_809_, size_t v_sz_810_, size_t v_i_811_, lean_object* v_b_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = lean_usize_dec_lt(v_i_811_, v_sz_810_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_goal_808_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_b_812_);
return v___x_819_;
}
else
{
lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_869_; 
v_snd_820_ = lean_ctor_get(v_b_812_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_b_812_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_b_812_, 0);
lean_dec(v_unused_870_);
v___x_822_ = v_b_812_;
v_isShared_823_ = v_isSharedCheck_869_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_dec(v_b_812_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_869_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_824_ = lean_array_uget_borrowed(v_as_809_, v_i_811_);
lean_inc(v_a_824_);
lean_inc_ref(v_goal_808_);
v___x_825_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_808_, v_a_824_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; lean_object* v_a_829_; uint8_t v___x_836_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref(v___x_825_);
v___x_827_ = lean_box(0);
v___x_836_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_826_);
if (v___x_836_ == 0)
{
lean_dec(v_a_826_);
v_a_829_ = v_snd_820_;
goto v___jp_828_;
}
else
{
lean_object* v___x_837_; 
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v_a_826_);
v___x_837_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_826_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
if (v___x_839_ == 0)
{
lean_dec(v_a_826_);
v_a_829_ = v_snd_820_;
goto v___jp_828_;
}
else
{
lean_object* v_self_840_; lean_object* v___x_841_; 
v_self_840_ = lean_ctor_get(v_a_826_, 0);
lean_inc_ref(v_self_840_);
lean_dec(v_a_826_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc_ref(v_self_840_);
lean_inc_ref(v_goal_808_);
v___x_841_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_808_, v_self_840_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
if (lean_obj_tag(v_a_842_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; 
v_val_843_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref(v_a_842_);
lean_inc_ref(v_goal_808_);
v___x_844_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_808_, v_self_840_, v_val_843_, v_snd_820_);
v_a_829_ = v___x_844_;
goto v___jp_828_;
}
else
{
lean_dec(v_a_842_);
lean_dec_ref(v_self_840_);
v_a_829_ = v_snd_820_;
goto v___jp_828_;
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v_self_840_);
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_goal_808_);
v_a_845_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_841_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_826_);
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_goal_808_);
v_a_853_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_837_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_837_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
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
v___jp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_a_829_);
lean_ctor_set(v___x_822_, 0, v___x_827_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_a_829_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_811_, v___x_832_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_808_, v_as_809_, v_sz_810_, v___x_833_, v___x_831_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_834_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_goal_808_);
v_a_861_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_825_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_825_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_871_, lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
size_t v_sz_boxed_881_; size_t v_i_boxed_882_; lean_object* v_res_883_; 
v_sz_boxed_881_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_882_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_871_, v_as_872_, v_sz_boxed_881_, v_i_boxed_882_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec_ref(v_as_872_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_884_, lean_object* v_t_885_, lean_object* v_init_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_root_892_; lean_object* v_tail_893_; lean_object* v___x_894_; 
v_root_892_ = lean_ctor_get(v_t_885_, 0);
lean_inc_ref(v_root_892_);
v_tail_893_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_tail_893_);
lean_dec_ref(v_t_885_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc_ref(v_init_886_);
lean_inc_ref(v_goal_884_);
v___x_894_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_goal_884_, v_init_886_, v_root_892_, v_init_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec_ref(v_init_886_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_931_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_931_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_931_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_931_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; 
lean_dec_ref(v_tail_893_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec_ref(v_goal_884_);
v_a_899_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v_a_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_897_);
v_a_903_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v_a_895_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_a_903_);
v_sz_906_ = lean_array_size(v_tail_893_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_884_, v_tail_893_, v_sz_906_, v___x_907_, v___x_905_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec_ref(v_tail_893_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_922_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_922_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_922_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_922_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_fst_913_; 
v_fst_913_ = lean_ctor_get(v_a_909_, 0);
if (lean_obj_tag(v_fst_913_) == 0)
{
lean_object* v_snd_914_; lean_object* v___x_916_; 
v_snd_914_ = lean_ctor_get(v_a_909_, 1);
lean_inc(v_snd_914_);
lean_dec(v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_snd_914_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_snd_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; 
lean_inc_ref(v_fst_913_);
lean_dec(v_a_909_);
v_val_918_ = lean_ctor_get(v_fst_913_, 0);
lean_inc(v_val_918_);
lean_dec_ref(v_fst_913_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_val_918_);
v___x_920_ = v___x_911_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_val_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_908_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_908_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_tail_893_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec_ref(v_goal_884_);
v_a_932_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_894_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_894_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_940_, lean_object* v_t_941_, lean_object* v_init_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_940_, v_t_941_, v_init_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
if (lean_obj_tag(v_x_950_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = lean_box(0);
return v___x_951_;
}
else
{
lean_object* v_key_952_; lean_object* v_value_953_; lean_object* v_tail_954_; uint8_t v___x_955_; 
v_key_952_ = lean_ctor_get(v_x_950_, 0);
v_value_953_ = lean_ctor_get(v_x_950_, 1);
v_tail_954_ = lean_ctor_get(v_x_950_, 2);
v___x_955_ = lean_expr_eqv(v_key_952_, v_a_949_);
if (v___x_955_ == 0)
{
v_x_950_ = v_tail_954_;
goto _start;
}
else
{
lean_object* v___x_957_; 
lean_inc(v_value_953_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_value_953_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_a_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_buckets_963_; lean_object* v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v_fold_968_; uint64_t v___x_969_; uint64_t v___x_970_; uint64_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_buckets_963_ = lean_ctor_get(v_m_961_, 1);
v___x_964_ = lean_array_get_size(v_buckets_963_);
v___x_965_ = l_Lean_Expr_hash(v_a_962_);
v___x_966_ = 32ULL;
v___x_967_ = lean_uint64_shift_right(v___x_965_, v___x_966_);
v_fold_968_ = lean_uint64_xor(v___x_965_, v___x_967_);
v___x_969_ = 16ULL;
v___x_970_ = lean_uint64_shift_right(v_fold_968_, v___x_969_);
v___x_971_ = lean_uint64_xor(v_fold_968_, v___x_970_);
v___x_972_ = lean_uint64_to_usize(v___x_971_);
v___x_973_ = lean_usize_of_nat(v___x_964_);
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_sub(v___x_973_, v___x_974_);
v___x_976_ = lean_usize_land(v___x_972_, v___x_975_);
v___x_977_ = lean_array_uget_borrowed(v_buckets_963_, v___x_976_);
v___x_978_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_962_, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_979_, v_a_980_);
lean_dec_ref(v_a_980_);
lean_dec_ref(v_m_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(lean_object* v_goal_982_, lean_object* v_as_983_, size_t v_sz_984_, size_t v_i_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_985_, v_sz_984_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_dec_ref(v_goal_982_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_b_986_);
return v___x_993_;
}
else
{
lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1025_; 
v_snd_994_ = lean_ctor_get(v_b_986_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_b_986_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_b_986_, 0);
lean_dec(v_unused_1026_);
v___x_996_ = v_b_986_;
v_isShared_997_ = v_isSharedCheck_1025_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_dec(v_b_986_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1025_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_array_uget_borrowed(v_as_983_, v_i_985_);
lean_inc(v_a_998_);
lean_inc_ref(v_goal_982_);
v___x_999_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_982_, v_a_998_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_self_1001_; lean_object* v___x_1002_; lean_object* v_a_1004_; lean_object* v___x_1011_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v_self_1001_ = lean_ctor_get(v_a_1000_, 0);
lean_inc_ref(v_self_1001_);
lean_dec(v_a_1000_);
v___x_1002_ = lean_box(0);
lean_inc_ref(v_self_1001_);
v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1001_);
if (lean_obj_tag(v___x_1011_) == 1)
{
lean_object* v_val_1012_; lean_object* v___x_1013_; 
v_val_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_994_, v_val_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_994_, v_self_1001_);
lean_dec_ref(v_self_1001_);
if (lean_obj_tag(v___x_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1016_; 
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref(v___x_1014_);
lean_inc_ref(v_goal_982_);
v___x_1016_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_982_, v_val_1012_, v_val_1015_, v_snd_994_);
v_a_1004_ = v___x_1016_;
goto v___jp_1003_;
}
else
{
lean_dec(v___x_1014_);
lean_dec(v_val_1012_);
v_a_1004_ = v_snd_994_;
goto v___jp_1003_;
}
}
else
{
lean_dec_ref(v___x_1013_);
lean_dec(v_val_1012_);
lean_dec_ref(v_self_1001_);
v_a_1004_ = v_snd_994_;
goto v___jp_1003_;
}
}
else
{
lean_dec(v___x_1011_);
lean_dec_ref(v_self_1001_);
v_a_1004_ = v_snd_994_;
goto v___jp_1003_;
}
v___jp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v_a_1004_);
lean_ctor_set(v___x_996_, 0, v___x_1002_);
v___x_1006_ = v___x_996_;
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
size_t v___x_1007_; size_t v___x_1008_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_985_, v___x_1007_);
v_i_985_ = v___x_1008_;
v_b_986_ = v___x_1006_;
goto _start;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_del_object(v___x_996_);
lean_dec(v_snd_994_);
lean_dec_ref(v_goal_982_);
v_a_1017_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_999_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_999_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12___boxed(lean_object* v_goal_1027_, lean_object* v_as_1028_, lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_1027_, v_as_1028_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1028_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(lean_object* v_goal_1040_, lean_object* v_as_1041_, size_t v_sz_1042_, size_t v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_usize_dec_lt(v_i_1043_, v_sz_1042_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec_ref(v_goal_1040_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1044_);
return v___x_1051_;
}
else
{
lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1083_; 
v_snd_1052_ = lean_ctor_get(v_b_1044_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_b_1044_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_b_1044_, 0);
lean_dec(v_unused_1084_);
v___x_1054_ = v_b_1044_;
v_isShared_1055_ = v_isSharedCheck_1083_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_dec(v_b_1044_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1083_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_array_uget_borrowed(v_as_1041_, v_i_1043_);
lean_inc(v_a_1056_);
lean_inc_ref(v_goal_1040_);
v___x_1057_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1040_, v_a_1056_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_self_1059_; lean_object* v___x_1060_; lean_object* v_a_1062_; lean_object* v___x_1069_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v_self_1059_ = lean_ctor_get(v_a_1058_, 0);
lean_inc_ref(v_self_1059_);
lean_dec(v_a_1058_);
v___x_1060_ = lean_box(0);
lean_inc_ref(v_self_1059_);
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1059_);
if (lean_obj_tag(v___x_1069_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1052_, v_val_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1052_, v_self_1059_);
lean_dec_ref(v_self_1059_);
if (lean_obj_tag(v___x_1072_) == 1)
{
lean_object* v_val_1073_; lean_object* v___x_1074_; 
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref(v___x_1072_);
lean_inc_ref(v_goal_1040_);
v___x_1074_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1040_, v_val_1070_, v_val_1073_, v_snd_1052_);
v_a_1062_ = v___x_1074_;
goto v___jp_1061_;
}
else
{
lean_dec(v___x_1072_);
lean_dec(v_val_1070_);
v_a_1062_ = v_snd_1052_;
goto v___jp_1061_;
}
}
else
{
lean_dec_ref(v___x_1071_);
lean_dec(v_val_1070_);
lean_dec_ref(v_self_1059_);
v_a_1062_ = v_snd_1052_;
goto v___jp_1061_;
}
}
else
{
lean_dec(v___x_1069_);
lean_dec_ref(v_self_1059_);
v_a_1062_ = v_snd_1052_;
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_a_1062_);
lean_ctor_set(v___x_1054_, 0, v___x_1060_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_a_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1043_, v___x_1065_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_1040_, v_as_1041_, v_sz_1042_, v___x_1066_, v___x_1064_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_del_object(v___x_1054_);
lean_dec(v_snd_1052_);
lean_dec_ref(v_goal_1040_);
v_a_1075_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1057_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1057_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10___boxed(lean_object* v_goal_1085_, lean_object* v_as_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_1085_, v_as_1086_, v_sz_boxed_1095_, v_i_boxed_1096_, v_b_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_as_1086_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(lean_object* v_goal_1098_, lean_object* v_inh_1099_, lean_object* v_n_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
if (lean_obj_tag(v_n_1100_) == 0)
{
lean_object* v_cs_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1141_; 
v_cs_1107_ = lean_ctor_get(v_n_1100_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_n_1100_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1109_ = v_n_1100_;
v_isShared_1110_ = v_isSharedCheck_1141_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_cs_1107_);
lean_dec(v_n_1100_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1141_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_b_1101_);
v_sz_1113_ = lean_array_size(v_cs_1107_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_goal_1098_, v_inh_1099_, v_cs_1107_, v_sz_1113_, v___x_1114_, v___x_1112_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v_cs_1107_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1132_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1132_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1132_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_fst_1120_; 
v_fst_1120_ = lean_ctor_get(v_a_1116_, 0);
if (lean_obj_tag(v_fst_1120_) == 0)
{
lean_object* v_snd_1121_; lean_object* v___x_1123_; 
v_snd_1121_ = lean_ctor_get(v_a_1116_, 1);
lean_inc(v_snd_1121_);
lean_dec(v_a_1116_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 1);
lean_ctor_set(v___x_1109_, 0, v_snd_1121_);
v___x_1123_ = v___x_1109_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_snd_1121_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1123_);
v___x_1125_ = v___x_1118_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; 
lean_inc_ref(v_fst_1120_);
lean_dec(v_a_1116_);
lean_del_object(v___x_1109_);
v_val_1128_ = lean_ctor_get(v_fst_1120_, 0);
lean_inc(v_val_1128_);
lean_dec_ref(v_fst_1120_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v_val_1128_);
v___x_1130_ = v___x_1118_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_val_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_del_object(v___x_1109_);
v_a_1133_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1115_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1115_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
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
else
{
lean_object* v_vs_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1176_; 
v_vs_1142_ = lean_ctor_get(v_n_1100_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_n_1100_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1144_ = v_n_1100_;
v_isShared_1145_ = v_isSharedCheck_1176_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_vs_1142_);
lean_dec(v_n_1100_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1176_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; size_t v_sz_1148_; size_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_b_1101_);
v_sz_1148_ = lean_array_size(v_vs_1142_);
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_1098_, v_vs_1142_, v_sz_1148_, v___x_1149_, v___x_1147_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v_vs_1142_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1167_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1167_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; 
v_fst_1155_ = lean_ctor_get(v_a_1151_, 0);
if (lean_obj_tag(v_fst_1155_) == 0)
{
lean_object* v_snd_1156_; lean_object* v___x_1158_; 
v_snd_1156_ = lean_ctor_get(v_a_1151_, 1);
lean_inc(v_snd_1156_);
lean_dec(v_a_1151_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_snd_1156_);
v___x_1158_ = v___x_1144_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_snd_1156_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1158_);
v___x_1160_ = v___x_1153_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1165_; 
lean_inc_ref(v_fst_1155_);
lean_dec(v_a_1151_);
lean_del_object(v___x_1144_);
v_val_1163_ = lean_ctor_get(v_fst_1155_, 0);
lean_inc(v_val_1163_);
lean_dec_ref(v_fst_1155_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_val_1163_);
v___x_1165_ = v___x_1153_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_val_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1144_);
v_a_1168_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1150_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1150_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(lean_object* v_goal_1177_, lean_object* v_inh_1178_, lean_object* v_as_1179_, size_t v_sz_1180_, size_t v_i_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_lt(v_i_1181_, v_sz_1180_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_goal_1177_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_b_1182_);
return v___x_1189_;
}
else
{
lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1224_; 
v_snd_1190_ = lean_ctor_get(v_b_1182_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_b_1182_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_b_1182_, 0);
lean_dec(v_unused_1225_);
v___x_1192_ = v_b_1182_;
v_isShared_1193_ = v_isSharedCheck_1224_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_dec(v_b_1182_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1224_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_array_uget_borrowed(v_as_1179_, v_i_1181_);
lean_inc(v_snd_1190_);
lean_inc(v_a_1194_);
lean_inc_ref(v_goal_1177_);
v___x_1195_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_goal_1177_, v_inh_1178_, v_a_1194_, v_snd_1190_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1215_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
if (lean_obj_tag(v_a_1196_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_dec_ref(v_goal_1177_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_a_1196_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1200_);
v___x_1202_ = v___x_1192_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_snd_1190_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_del_object(v___x_1198_);
lean_dec(v_snd_1190_);
v_a_1207_ = lean_ctor_get(v_a_1196_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v_a_1196_);
v___x_1208_ = lean_box(0);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_a_1207_);
lean_ctor_set(v___x_1192_, 0, v___x_1208_);
v___x_1210_ = v___x_1192_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_a_1207_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
size_t v___x_1211_; size_t v___x_1212_; 
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1181_, v___x_1211_);
v_i_1181_ = v___x_1212_;
v_b_1182_ = v___x_1210_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1192_);
lean_dec(v_snd_1190_);
lean_dec_ref(v_goal_1177_);
v_a_1216_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1195_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1195_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9___boxed(lean_object* v_goal_1226_, lean_object* v_inh_1227_, lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_goal_1226_, v_inh_1227_, v_as_1228_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec_ref(v_as_1228_);
lean_dec_ref(v_inh_1227_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5___boxed(lean_object* v_goal_1240_, lean_object* v_inh_1241_, lean_object* v_n_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_goal_1240_, v_inh_1241_, v_n_1242_, v_b_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v_inh_1241_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(lean_object* v_goal_1250_, lean_object* v_as_1251_, size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v_goal_1250_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_b_1254_);
return v___x_1261_;
}
else
{
lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1293_; 
v_snd_1262_ = lean_ctor_get(v_b_1254_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_b_1254_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_b_1254_, 0);
lean_dec(v_unused_1294_);
v___x_1264_ = v_b_1254_;
v_isShared_1265_ = v_isSharedCheck_1293_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_dec(v_b_1254_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1293_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_array_uget_borrowed(v_as_1251_, v_i_1253_);
lean_inc(v_a_1266_);
lean_inc_ref(v_goal_1250_);
v___x_1267_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1250_, v_a_1266_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_self_1269_; lean_object* v___x_1270_; lean_object* v_a_1272_; lean_object* v___x_1279_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref(v___x_1267_);
v_self_1269_ = lean_ctor_get(v_a_1268_, 0);
lean_inc_ref(v_self_1269_);
lean_dec(v_a_1268_);
v___x_1270_ = lean_box(0);
lean_inc_ref(v_self_1269_);
v___x_1279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1269_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1281_; 
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1262_, v_val_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1262_, v_self_1269_);
lean_dec_ref(v_self_1269_);
if (lean_obj_tag(v___x_1282_) == 1)
{
lean_object* v_val_1283_; lean_object* v___x_1284_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref(v___x_1282_);
lean_inc_ref(v_goal_1250_);
v___x_1284_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1250_, v_val_1280_, v_val_1283_, v_snd_1262_);
v_a_1272_ = v___x_1284_;
goto v___jp_1271_;
}
else
{
lean_dec(v___x_1282_);
lean_dec(v_val_1280_);
v_a_1272_ = v_snd_1262_;
goto v___jp_1271_;
}
}
else
{
lean_dec_ref(v___x_1281_);
lean_dec(v_val_1280_);
lean_dec_ref(v_self_1269_);
v_a_1272_ = v_snd_1262_;
goto v___jp_1271_;
}
}
else
{
lean_dec(v___x_1279_);
lean_dec_ref(v_self_1269_);
v_a_1272_ = v_snd_1262_;
goto v___jp_1271_;
}
v___jp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_a_1272_);
lean_ctor_set(v___x_1264_, 0, v___x_1270_);
v___x_1274_ = v___x_1264_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_a_1272_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
size_t v___x_1275_; size_t v___x_1276_; 
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_add(v_i_1253_, v___x_1275_);
v_i_1253_ = v___x_1276_;
v_b_1254_ = v___x_1274_;
goto _start;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1264_);
lean_dec(v_snd_1262_);
lean_dec_ref(v_goal_1250_);
v_a_1285_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1267_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1267_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12___boxed(lean_object* v_goal_1295_, lean_object* v_as_1296_, lean_object* v_sz_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1297_);
lean_dec(v_sz_1297_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_1295_, v_as_1296_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_as_1296_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(lean_object* v_goal_1308_, lean_object* v_as_1309_, size_t v_sz_1310_, size_t v_i_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1311_, v_sz_1310_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref(v_goal_1308_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_b_1312_);
return v___x_1319_;
}
else
{
lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1351_; 
v_snd_1320_ = lean_ctor_get(v_b_1312_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_b_1312_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v_b_1312_, 0);
lean_dec(v_unused_1352_);
v___x_1322_ = v_b_1312_;
v_isShared_1323_ = v_isSharedCheck_1351_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_dec(v_b_1312_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1351_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1324_ = lean_array_uget_borrowed(v_as_1309_, v_i_1311_);
lean_inc(v_a_1324_);
lean_inc_ref(v_goal_1308_);
v___x_1325_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1308_, v_a_1324_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_self_1327_; lean_object* v___x_1328_; lean_object* v_a_1330_; lean_object* v___x_1337_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v_self_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_self_1327_);
lean_dec(v_a_1326_);
v___x_1328_ = lean_box(0);
lean_inc_ref(v_self_1327_);
v___x_1337_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1327_);
if (lean_obj_tag(v___x_1337_) == 1)
{
lean_object* v_val_1338_; lean_object* v___x_1339_; 
v_val_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1320_, v_val_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1320_, v_self_1327_);
lean_dec_ref(v_self_1327_);
if (lean_obj_tag(v___x_1340_) == 1)
{
lean_object* v_val_1341_; lean_object* v___x_1342_; 
v_val_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_val_1341_);
lean_dec_ref(v___x_1340_);
lean_inc_ref(v_goal_1308_);
v___x_1342_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1308_, v_val_1338_, v_val_1341_, v_snd_1320_);
v_a_1330_ = v___x_1342_;
goto v___jp_1329_;
}
else
{
lean_dec(v___x_1340_);
lean_dec(v_val_1338_);
v_a_1330_ = v_snd_1320_;
goto v___jp_1329_;
}
}
else
{
lean_dec_ref(v___x_1339_);
lean_dec(v_val_1338_);
lean_dec_ref(v_self_1327_);
v_a_1330_ = v_snd_1320_;
goto v___jp_1329_;
}
}
else
{
lean_dec(v___x_1337_);
lean_dec_ref(v_self_1327_);
v_a_1330_ = v_snd_1320_;
goto v___jp_1329_;
}
v___jp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_a_1330_);
lean_ctor_set(v___x_1322_, 0, v___x_1328_);
v___x_1332_ = v___x_1322_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_a_1330_);
v___x_1332_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1311_, v___x_1333_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_1308_, v_as_1309_, v_sz_1310_, v___x_1334_, v___x_1332_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1322_);
lean_dec(v_snd_1320_);
lean_dec_ref(v_goal_1308_);
v_a_1343_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1325_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1325_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6___boxed(lean_object* v_goal_1353_, lean_object* v_as_1354_, lean_object* v_sz_1355_, lean_object* v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
size_t v_sz_boxed_1363_; size_t v_i_boxed_1364_; lean_object* v_res_1365_; 
v_sz_boxed_1363_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_i_boxed_1364_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_1353_, v_as_1354_, v_sz_boxed_1363_, v_i_boxed_1364_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1366_, lean_object* v_t_1367_, lean_object* v_init_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_root_1374_; lean_object* v_tail_1375_; lean_object* v___x_1376_; 
v_root_1374_ = lean_ctor_get(v_t_1367_, 0);
lean_inc_ref(v_root_1374_);
v_tail_1375_ = lean_ctor_get(v_t_1367_, 1);
lean_inc_ref(v_tail_1375_);
lean_dec_ref(v_t_1367_);
lean_inc_ref(v_init_1368_);
lean_inc_ref(v_goal_1366_);
v___x_1376_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_goal_1366_, v_init_1368_, v_root_1374_, v_init_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_init_1368_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1413_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1413_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1413_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
if (lean_obj_tag(v_a_1377_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; 
lean_dec_ref(v_tail_1375_);
lean_dec_ref(v_goal_1366_);
v_a_1381_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v_a_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_a_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
lean_del_object(v___x_1379_);
v_a_1385_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v_a_1377_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1385_);
v_sz_1388_ = lean_array_size(v_tail_1375_);
v___x_1389_ = ((size_t)0ULL);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_1366_, v_tail_1375_, v_sz_1388_, v___x_1389_, v___x_1387_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref(v_tail_1375_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1404_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_fst_1395_; 
v_fst_1395_ = lean_ctor_get(v_a_1391_, 0);
if (lean_obj_tag(v_fst_1395_) == 0)
{
lean_object* v_snd_1396_; lean_object* v___x_1398_; 
v_snd_1396_ = lean_ctor_get(v_a_1391_, 1);
lean_inc(v_snd_1396_);
lean_dec(v_a_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_snd_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_snd_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1402_; 
lean_inc_ref(v_fst_1395_);
lean_dec(v_a_1391_);
v_val_1400_ = lean_ctor_get(v_fst_1395_, 0);
lean_inc(v_val_1400_);
lean_dec_ref(v_fst_1395_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_val_1400_);
v___x_1402_ = v___x_1393_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1400_);
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
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1390_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1390_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_tail_1375_);
lean_dec_ref(v_goal_1366_);
v_a_1414_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1376_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1376_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object* v_goal_1422_, lean_object* v_t_1423_, lean_object* v_init_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1422_, v_t_1423_, v_init_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_unsigned_to_nat(16u);
v___x_1433_ = lean_mk_array(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_model_1436_; 
v___x_1434_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0);
v___x_1435_ = lean_unsigned_to_nat(0u);
v_model_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_1436_, 0, v___x_1435_);
lean_ctor_set(v_model_1436_, 1, v___x_1434_);
return v_model_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_toGoalState_1451_; lean_object* v_exprs_1452_; lean_object* v_model_1453_; lean_object* v___x_1454_; 
v_toGoalState_1451_ = lean_ctor_get(v_goal_1445_, 0);
v_exprs_1452_ = lean_ctor_get(v_toGoalState_1451_, 3);
v_model_1453_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1);
lean_inc(v_a_1449_);
lean_inc_ref(v_a_1448_);
lean_inc(v_a_1447_);
lean_inc_ref(v_a_1446_);
lean_inc_ref(v_exprs_1452_);
lean_inc_ref(v_goal_1445_);
v___x_1454_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1445_, v_exprs_1452_, v_model_1453_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
lean_inc_ref(v_exprs_1452_);
lean_inc_ref(v_goal_1445_);
v___x_1456_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1445_, v_exprs_1452_, v_a_1455_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2));
lean_inc(v_a_1449_);
lean_inc_ref(v_a_1448_);
lean_inc(v_a_1447_);
lean_inc_ref(v_a_1446_);
v___x_1459_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1445_, v___x_1458_, v_a_1457_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6));
v___x_1462_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_1461_, v_a_1460_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1470_);
v___x_1464_ = v___x_1462_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v___x_1462_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_a_1460_);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1460_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1460_);
v_a_1471_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v___x_1459_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_goal_1445_);
v_a_1479_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1456_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1456_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_goal_1445_);
v_a_1487_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1454_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1454_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1502_, lean_object* v_m_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1503_, v_a_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1506_, lean_object* v_m_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1506_, v_m_1507_, v_a_1508_);
lean_dec_ref(v_a_1508_);
lean_dec_ref(v_m_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1511_, v_x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1514_, lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1514_, v_a_1515_, v_x_1516_);
lean_dec(v_x_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1517_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
}
#ifdef __cplusplus
}
#endif

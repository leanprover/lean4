// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Diseq
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Lemmas
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
uint64_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Diseq"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.Grind.mkDiseqProofUsing"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "ne_of_ne_of_eq_right"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value),LEAN_SCALAR_PTR_LITERAL(74, 75, 151, 179, 29, 111, 89, 209)}};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ne_of_ne_of_eq_left"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value),LEAN_SCALAR_PTR_LITERAL(163, 56, 30, 117, 227, 52, 169, 167)}};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value),LEAN_SCALAR_PTR_LITERAL(106, 137, 24, 74, 49, 62, 0, 94)}};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "internal `grind` error, failed to build disequality proof for"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProof___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkDiseqProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkDiseqProof___closed__1;
static const lean_string_object l_Lean_Meta_Grind_mkDiseqProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nand"};
static const lean_object* l_Lean_Meta_Grind_mkDiseqProof___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkDiseqProof___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkDiseqProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkDiseqProof___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = l_Lean_Level_ofNat(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2);
v___x_8_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3, &l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3);
v___x_10_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1));
v___x_11_ = l_Lean_mkConst(v___x_10_, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6));
v___x_17_ = l_Lean_Expr_const___override(v___x_16_, v___x_15_);
return v___x_17_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7, &l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7);
v___x_19_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4, &l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4);
v___x_20_ = l_Lean_Expr_app___override(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8, &l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v___x_22_, lean_object* v_keys_23_, lean_object* v_vals_24_, lean_object* v_i_25_, lean_object* v_k_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_array_get_size(v_keys_23_);
v___x_28_ = lean_nat_dec_lt(v_i_25_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_dec_ref(v_k_26_);
lean_dec(v_i_25_);
v___x_29_ = lean_box(0);
return v___x_29_;
}
else
{
lean_object* v_k_x27_30_; uint8_t v___x_31_; 
v_k_x27_30_ = lean_array_fget_borrowed(v_keys_23_, v_i_25_);
lean_inc(v_k_x27_30_);
lean_inc_ref(v_k_26_);
v___x_31_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_22_, v_k_26_, v_k_x27_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_add(v_i_25_, v___x_32_);
lean_dec(v_i_25_);
v_i_25_ = v___x_33_;
goto _start;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v_k_26_);
v___x_35_ = lean_array_fget_borrowed(v_vals_24_, v_i_25_);
lean_dec(v_i_25_);
lean_inc(v___x_35_);
lean_inc(v_k_x27_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_k_x27_30_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_38_, lean_object* v_keys_39_, lean_object* v_vals_40_, lean_object* v_i_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_38_, v_keys_39_, v_vals_40_, v_i_41_, v_k_42_);
lean_dec_ref(v_vals_40_);
lean_dec_ref(v_keys_39_);
lean_dec_ref(v___x_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(lean_object* v___x_44_, lean_object* v_x_45_, size_t v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_es_48_; lean_object* v___x_49_; size_t v___x_50_; size_t v___x_51_; lean_object* v_j_52_; lean_object* v___x_53_; 
v_es_48_ = lean_ctor_get(v_x_45_, 0);
lean_inc_ref(v_es_48_);
lean_dec_ref_known(v_x_45_, 1);
v___x_49_ = lean_box(2);
v___x_50_ = ((size_t)31ULL);
v___x_51_ = lean_usize_land(v_x_46_, v___x_50_);
v_j_52_ = lean_usize_to_nat(v___x_51_);
v___x_53_ = lean_array_get(v___x_49_, v_es_48_, v_j_52_);
lean_dec(v_j_52_);
lean_dec_ref(v_es_48_);
switch(lean_obj_tag(v___x_53_))
{
case 0:
{
lean_object* v_key_54_; lean_object* v_val_55_; uint8_t v___x_56_; 
v_key_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_n(v_key_54_, 2);
v_val_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc(v_val_55_);
lean_dec_ref_known(v___x_53_, 2);
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_44_, v_x_47_, v_key_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec(v_val_55_);
lean_dec(v_key_54_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_key_54_);
lean_ctor_set(v___x_58_, 1, v_val_55_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
case 1:
{
lean_object* v_node_60_; size_t v___x_61_; size_t v___x_62_; 
v_node_60_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_node_60_);
lean_dec_ref_known(v___x_53_, 1);
v___x_61_ = ((size_t)5ULL);
v___x_62_ = lean_usize_shift_right(v_x_46_, v___x_61_);
v_x_45_ = v_node_60_;
v_x_46_ = v___x_62_;
goto _start;
}
default: 
{
lean_object* v___x_64_; 
lean_dec_ref(v_x_47_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
}
else
{
lean_object* v_ks_65_; lean_object* v_vs_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_ks_65_ = lean_ctor_get(v_x_45_, 0);
lean_inc_ref(v_ks_65_);
v_vs_66_ = lean_ctor_get(v_x_45_, 1);
lean_inc_ref(v_vs_66_);
lean_dec_ref_known(v_x_45_, 2);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_44_, v_ks_65_, v_vs_66_, v___x_67_, v_x_47_);
lean_dec_ref(v_vs_66_);
lean_dec_ref(v_ks_65_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(lean_object* v___x_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
size_t v_x_4757__boxed_73_; lean_object* v_res_74_; 
v_x_4757__boxed_73_ = lean_unbox_usize(v_x_71_);
lean_dec(v_x_71_);
v_res_74_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_69_, v_x_70_, v_x_4757__boxed_73_, v_x_72_);
lean_dec_ref(v___x_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(lean_object* v___x_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
uint64_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; 
lean_inc_ref(v_x_77_);
v___x_78_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_75_, v_x_77_);
v___x_79_ = lean_uint64_to_usize(v___x_78_);
lean_inc_ref(v_x_76_);
v___x_80_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_75_, v_x_76_, v___x_79_, v_x_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg___boxed(lean_object* v___x_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_81_, v_x_82_, v_x_83_);
lean_dec_ref(v_x_82_);
lean_dec_ref(v___x_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(lean_object* v_a_85_, lean_object* v_b_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_toGoalState_95_; lean_object* v_enodeMap_96_; lean_object* v_congrTable_97_; lean_object* v___x_98_; lean_object* v_key_99_; lean_object* v___x_100_; 
v___x_94_ = lean_st_ref_get(v_a_87_);
v_toGoalState_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_toGoalState_95_);
lean_dec(v___x_94_);
v_enodeMap_96_ = lean_ctor_get(v_toGoalState_95_, 1);
lean_inc_ref(v_enodeMap_96_);
v_congrTable_97_ = lean_ctor_get(v_toGoalState_95_, 4);
lean_inc_ref(v_congrTable_97_);
lean_dec_ref(v_toGoalState_95_);
v___x_98_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
v_key_99_ = l_Lean_mkAppB(v___x_98_, v_a_85_, v_b_86_);
v___x_100_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v_enodeMap_96_, v_congrTable_97_, v_key_99_);
lean_dec_ref(v_congrTable_97_);
lean_dec_ref(v_enodeMap_96_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_133_; 
v_val_103_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_133_ == 0)
{
v___x_105_ = v___x_100_;
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v___x_100_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_fst_107_; lean_object* v___x_108_; 
v_fst_107_ = lean_ctor_get(v_val_103_, 0);
lean_inc_n(v_fst_107_, 2);
lean_dec(v_val_103_);
v___x_108_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_107_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_124_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_124_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_124_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
uint8_t v___x_113_; 
v___x_113_ = lean_unbox(v_a_109_);
lean_dec(v_a_109_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v_fst_107_);
lean_del_object(v___x_105_);
v___x_114_ = lean_box(0);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_119_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v_fst_107_);
v___x_119_ = v___x_105_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_fst_107_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_119_);
v___x_121_ = v___x_111_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec(v_fst_107_);
lean_del_object(v___x_105_);
v_a_125_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_108_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_108_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(lean_object* v_a_134_, lean_object* v_b_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_134_, v_b_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f(lean_object* v_a_144_, lean_object* v_b_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_144_, v_b_145_, v_a_146_, v_a_150_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object* v_a_158_, lean_object* v_b_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_Grind_getDiseqFor_x3f(v_a_158_, v_b_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec(v_a_160_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(lean_object* v___x_172_, lean_object* v_00_u03b2_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_172_, v_x_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___boxed(lean_object* v___x_177_, lean_object* v_00_u03b2_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(v___x_177_, v_00_u03b2_178_, v_x_179_, v_x_180_);
lean_dec_ref(v_x_179_);
lean_dec_ref(v___x_177_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(lean_object* v___x_182_, lean_object* v_00_u03b2_183_, lean_object* v_x_184_, size_t v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
lean_inc_ref(v_x_184_);
v___x_187_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_182_, v_x_184_, v_x_185_, v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(lean_object* v___x_188_, lean_object* v_00_u03b2_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_4916__boxed_193_; lean_object* v_res_194_; 
v_x_4916__boxed_193_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_194_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(v___x_188_, v_00_u03b2_189_, v_x_190_, v_x_4916__boxed_193_, v_x_192_);
lean_dec_ref(v_x_190_);
lean_dec_ref(v___x_188_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(lean_object* v___x_195_, lean_object* v_00_u03b2_196_, lean_object* v_keys_197_, lean_object* v_vals_198_, lean_object* v_heq_199_, lean_object* v_i_200_, lean_object* v_k_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_195_, v_keys_197_, v_vals_198_, v_i_200_, v_k_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_203_, lean_object* v_00_u03b2_204_, lean_object* v_keys_205_, lean_object* v_vals_206_, lean_object* v_heq_207_, lean_object* v_i_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(v___x_203_, v_00_u03b2_204_, v_keys_205_, v_vals_206_, v_heq_207_, v_i_208_, v_k_209_);
lean_dec_ref(v_vals_206_);
lean_dec_ref(v_keys_205_);
lean_dec_ref(v___x_203_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg(lean_object* v_a_211_, lean_object* v_b_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_211_, v_b_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_235_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_235_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
if (lean_obj_tag(v_a_221_) == 0)
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = 0;
v___x_226_ = lean_box(v___x_225_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec_ref_known(v_a_221_, 1);
v___x_230_ = 1;
v___x_231_ = lean_box(v___x_230_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_231_);
v___x_233_ = v___x_223_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_a_236_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_220_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_220_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg___boxed(lean_object* v_a_244_, lean_object* v_b_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_244_, v_b_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_254_, v_b_255_, v_a_256_, v_a_260_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_Grind_isDiseq(v_a_268_, v_b_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_a_270_);
return v_res_281_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(lean_object* v_msg_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_12288__overap_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0);
v___x_12288__overap_296_ = lean_panic_fn_borrowed(v___x_295_, v_msg_283_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
lean_inc(v___y_285_);
lean_inc(v___y_284_);
v___x_297_ = lean_apply_11(v___x_12288__overap_296_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, lean_box(0));
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec(v___y_299_);
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_314_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2));
v___x_315_ = lean_unsigned_to_nat(30u);
v___x_316_ = lean_unsigned_to_nat(44u);
v___x_317_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1));
v___x_318_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0));
v___x_319_ = l_mkPanicMessageWithDecl(v___x_318_, v___x_317_, v___x_316_, v___x_315_, v___x_314_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object* v_a_337_, lean_object* v_b_338_, lean_object* v_eq_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___x_364_; uint8_t v___x_365_; 
lean_inc_ref(v_eq_339_);
v___x_364_ = l_Lean_Expr_cleanupAnnotations(v_eq_339_);
v___x_365_ = l_Lean_Expr_isApp(v___x_364_);
if (v___x_365_ == 0)
{
lean_dec_ref(v___x_364_);
lean_dec_ref(v_eq_339_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
v___y_352_ = v_a_340_;
v___y_353_ = v_a_341_;
v___y_354_ = v_a_342_;
v___y_355_ = v_a_343_;
v___y_356_ = v_a_344_;
v___y_357_ = v_a_345_;
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
goto v___jp_351_;
}
else
{
lean_object* v_arg_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_arg_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_arg_366_);
v___x_367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_364_);
v___x_368_ = l_Lean_Expr_isApp(v___x_367_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_367_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_eq_339_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
v___y_352_ = v_a_340_;
v___y_353_ = v_a_341_;
v___y_354_ = v_a_342_;
v___y_355_ = v_a_343_;
v___y_356_ = v_a_344_;
v___y_357_ = v_a_345_;
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
goto v___jp_351_;
}
else
{
lean_object* v_arg_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_arg_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc_ref(v_arg_369_);
v___x_370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_367_);
v___x_371_ = l_Lean_Expr_isApp(v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_370_);
lean_dec_ref(v_arg_369_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_eq_339_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
v___y_352_ = v_a_340_;
v___y_353_ = v_a_341_;
v___y_354_ = v_a_342_;
v___y_355_ = v_a_343_;
v___y_356_ = v_a_344_;
v___y_357_ = v_a_345_;
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
goto v___jp_351_;
}
else
{
lean_object* v_arg_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_arg_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc_ref(v_arg_372_);
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_370_);
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1));
v___x_375_ = l_Lean_Expr_isConstOf(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_369_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_eq_339_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
v___y_352_ = v_a_340_;
v___y_353_ = v_a_341_;
v___y_354_ = v_a_342_;
v___y_355_ = v_a_343_;
v___y_356_ = v_a_344_;
v___y_357_ = v_a_345_;
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
goto v___jp_351_;
}
else
{
lean_object* v___x_376_; 
lean_inc_ref(v_eq_339_);
v___x_376_ = l_Lean_Meta_Grind_mkEqFalseProof(v_eq_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_451_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_451_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_451_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_451_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_u_381_; lean_object* v___y_383_; lean_object* v_h_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v_fst_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___x_431_; lean_object* v___y_433_; lean_object* v___x_447_; 
v_u_381_ = l_Lean_Expr_constLevels_x21(v___x_373_);
lean_dec_ref(v___x_373_);
v___x_431_ = l_Lean_Meta_mkOfEqFalseCore(v_eq_339_, v_a_377_);
v___x_447_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_337_, v_arg_369_, v_a_340_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; uint8_t v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
v___x_449_ = lean_unbox(v_a_448_);
lean_dec(v_a_448_);
if (v___x_449_ == 0)
{
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
else
{
lean_object* v___x_450_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_450_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_338_, v_arg_366_, v_a_340_);
v___y_433_ = v___x_450_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
v___jp_382_:
{
uint8_t v___x_395_; 
v___x_395_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_b_338_, v___y_383_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_del_object(v___x_379_);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_383_);
lean_inc_ref(v_b_338_);
v___x_396_ = lean_grind_mk_eq_proof(v_b_338_, v___y_383_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_407_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_407_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_401_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7));
v___x_402_ = l_Lean_mkConst(v___x_401_, v_u_381_);
v___x_403_ = l_Lean_mkApp6(v___x_402_, v_arg_372_, v_b_338_, v_a_337_, v___y_383_, v_a_397_, v_h_384_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_403_);
v___x_405_ = v___x_399_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_dec_ref(v_h_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_u_381_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
return v___x_396_;
}
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v___y_383_);
lean_dec(v_u_381_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_h_384_);
v___x_409_ = v___x_379_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_h_384_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
v___jp_411_:
{
uint8_t v___x_425_; 
v___x_425_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_337_, v_fst_412_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v_fst_412_);
lean_inc_ref(v_a_337_);
v___x_426_ = lean_grind_mk_eq_proof(v_a_337_, v_fst_412_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9));
lean_inc(v_u_381_);
v___x_429_ = l_Lean_mkConst(v___x_428_, v_u_381_);
lean_inc_ref(v_fst_413_);
lean_inc_ref(v_a_337_);
lean_inc_ref(v_arg_372_);
v___x_430_ = l_Lean_mkApp6(v___x_429_, v_arg_372_, v_a_337_, v_fst_412_, v_fst_413_, v_a_427_, v_snd_414_);
v___y_383_ = v_fst_413_;
v_h_384_ = v___x_430_;
v___y_385_ = v___y_415_;
v___y_386_ = v___y_416_;
v___y_387_ = v___y_417_;
v___y_388_ = v___y_418_;
v___y_389_ = v___y_419_;
v___y_390_ = v___y_420_;
v___y_391_ = v___y_421_;
v___y_392_ = v___y_422_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
goto v___jp_382_;
}
else
{
lean_dec_ref(v_snd_414_);
lean_dec_ref(v_fst_413_);
lean_dec_ref(v_fst_412_);
lean_dec(v_u_381_);
lean_del_object(v___x_379_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
return v___x_426_;
}
}
else
{
lean_dec_ref(v_fst_412_);
v___y_383_ = v_fst_413_;
v_h_384_ = v_snd_414_;
v___y_385_ = v___y_415_;
v___y_386_ = v___y_416_;
v___y_387_ = v___y_417_;
v___y_388_ = v___y_418_;
v___y_389_ = v___y_419_;
v___y_390_ = v___y_420_;
v___y_391_ = v___y_421_;
v___y_392_ = v___y_422_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
goto v___jp_382_;
}
}
v___jp_432_:
{
if (lean_obj_tag(v___y_433_) == 0)
{
lean_object* v_a_434_; uint8_t v___x_435_; 
v_a_434_ = lean_ctor_get(v___y_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v___x_435_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12));
lean_inc(v_u_381_);
v___x_437_ = l_Lean_mkConst(v___x_436_, v_u_381_);
lean_inc_ref(v_arg_366_);
lean_inc_ref(v_arg_369_);
lean_inc_ref(v_arg_372_);
v___x_438_ = l_Lean_mkApp4(v___x_437_, v_arg_372_, v_arg_369_, v_arg_366_, v___x_431_);
v_fst_412_ = v_arg_366_;
v_fst_413_ = v_arg_369_;
v_snd_414_ = v___x_438_;
v___y_415_ = v_a_340_;
v___y_416_ = v_a_341_;
v___y_417_ = v_a_342_;
v___y_418_ = v_a_343_;
v___y_419_ = v_a_344_;
v___y_420_ = v_a_345_;
v___y_421_ = v_a_346_;
v___y_422_ = v_a_347_;
v___y_423_ = v_a_348_;
v___y_424_ = v_a_349_;
goto v___jp_411_;
}
else
{
v_fst_412_ = v_arg_369_;
v_fst_413_ = v_arg_366_;
v_snd_414_ = v___x_431_;
v___y_415_ = v_a_340_;
v___y_416_ = v_a_341_;
v___y_417_ = v_a_342_;
v___y_418_ = v_a_343_;
v___y_419_ = v_a_344_;
v___y_420_ = v_a_345_;
v___y_421_ = v_a_346_;
v___y_422_ = v_a_347_;
v___y_423_ = v_a_348_;
v___y_424_ = v_a_349_;
goto v___jp_411_;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v___x_431_);
lean_dec(v_u_381_);
lean_del_object(v___x_379_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_369_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
v_a_439_ = lean_ctor_get(v___y_433_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___y_433_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___y_433_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___y_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_369_);
lean_dec_ref(v_arg_366_);
lean_dec_ref(v_eq_339_);
lean_dec_ref(v_b_338_);
lean_dec_ref(v_a_337_);
return v___x_376_;
}
}
}
}
}
v___jp_351_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3, &l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3);
v___x_363_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v___x_362_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___boxed(lean_object* v_a_452_, lean_object* v_b_453_, lean_object* v_eq_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_452_, v_b_453_, v_eq_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec(v_a_455_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object* v_a_467_, lean_object* v_b_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; 
lean_inc_ref(v_b_468_);
lean_inc_ref(v_a_467_);
v___x_480_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_467_, v_b_468_, v_a_469_, v_a_473_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_514_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_514_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_514_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_514_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
if (lean_obj_tag(v_a_481_) == 1)
{
lean_object* v_val_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_483_);
v_val_485_ = lean_ctor_get(v_a_481_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_481_);
if (v_isSharedCheck_509_ == 0)
{
v___x_487_ = v_a_481_;
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_val_485_);
lean_dec(v_a_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_467_, v_b_468_, v_val_485_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_500_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_500_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_a_490_);
v___x_495_ = v___x_487_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_487_);
v_a_501_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_489_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_489_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
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
else
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_dec(v_a_481_);
lean_dec_ref(v_b_468_);
lean_dec_ref(v_a_467_);
v___x_510_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_510_);
v___x_512_ = v___x_483_;
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
else
{
lean_dec_ref(v_b_468_);
lean_dec_ref(v_a_467_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___boxed(lean_object* v_a_515_, lean_object* v_b_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_515_, v_b_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(lean_object* v_msgData_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_env_536_; lean_object* v___x_537_; lean_object* v_mctx_538_; lean_object* v_lctx_539_; lean_object* v_options_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_535_ = lean_st_ref_get(v___y_533_);
v_env_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_env_536_);
lean_dec(v___x_535_);
v___x_537_ = lean_st_ref_get(v___y_531_);
v_mctx_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc_ref(v_mctx_538_);
lean_dec(v___x_537_);
v_lctx_539_ = lean_ctor_get(v___y_530_, 2);
v_options_540_ = lean_ctor_get(v___y_532_, 2);
lean_inc_ref(v_options_540_);
lean_inc_ref(v_lctx_539_);
v___x_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_541_, 0, v_env_536_);
lean_ctor_set(v___x_541_, 1, v_mctx_538_);
lean_ctor_set(v___x_541_, 2, v_lctx_539_);
lean_ctor_set(v___x_541_, 3, v_options_540_);
v___x_542_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_msgData_529_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(lean_object* v_msgData_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msgData_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(lean_object* v_msg_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_ref_557_; lean_object* v___x_558_; lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_ref_557_ = lean_ctor_get(v___y_554_, 5);
v___x_558_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msg_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_inc(v_ref_557_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_ref_557_);
lean_ctor_set(v___x_563_, 1, v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 1);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg___boxed(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__0));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__2));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object* v_a_581_, lean_object* v_b_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; 
lean_inc_ref(v_b_582_);
lean_inc_ref(v_a_581_);
v___x_594_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_581_, v_b_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_611_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_611_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_a_595_) == 1)
{
lean_object* v_val_599_; lean_object* v___x_601_; 
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
v_val_599_ = lean_ctor_get(v_a_595_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v_a_595_, 1);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_val_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_val_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_597_);
lean_dec(v_a_595_);
v___x_603_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__1, &l_Lean_Meta_Grind_mkDiseqProof___closed__1_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1);
v___x_604_ = l_Lean_indentExpr(v_a_581_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__3, &l_Lean_Meta_Grind_mkDiseqProof___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_indentExpr(v_b_582_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v___x_609_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_610_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_b_582_);
lean_dec_ref(v_a_581_);
v_a_612_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_594_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_594_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof___boxed(lean_object* v_a_620_, lean_object* v_b_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_620_, v_b_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec(v_a_622_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(lean_object* v_00_u03b1_634_, lean_object* v_msg_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_635_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(v_00_u03b1_648_, v_msg_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
return v_res_661_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq = _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_instHashableCongrKey___private__1(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqCongrKey___private__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_22_);
v___x_29_ = lean_box(0);
return v___x_29_;
}
else
{
lean_object* v_k_x27_30_; uint8_t v___x_31_; 
v_k_x27_30_ = lean_array_fget_borrowed(v_keys_23_, v_i_25_);
lean_inc(v_k_x27_30_);
lean_inc_ref(v_k_26_);
lean_inc_ref(v___x_22_);
v___x_31_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_22_, v_k_26_, v_k_x27_30_);
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
lean_dec_ref(v___x_22_);
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
return v_res_43_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_44_; size_t v___x_45_; size_t v___x_46_; 
v___x_44_ = ((size_t)5ULL);
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_shift_left(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; 
v___x_47_ = ((size_t)1ULL);
v___x_48_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0);
v___x_49_ = lean_usize_sub(v___x_48_, v___x_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(lean_object* v___x_50_, lean_object* v_x_51_, size_t v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_es_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_82_; 
v_es_54_ = lean_ctor_get(v_x_51_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_82_ == 0)
{
v___x_56_ = v_x_51_;
v_isShared_57_ = v_isSharedCheck_82_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_es_54_);
lean_dec(v_x_51_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_82_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; lean_object* v_j_62_; lean_object* v___x_63_; 
v___x_58_ = lean_box(2);
v___x_59_ = ((size_t)5ULL);
v___x_60_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1);
v___x_61_ = lean_usize_land(v_x_52_, v___x_60_);
v_j_62_ = lean_usize_to_nat(v___x_61_);
v___x_63_ = lean_array_get(v___x_58_, v_es_54_, v_j_62_);
lean_dec(v_j_62_);
lean_dec_ref(v_es_54_);
switch(lean_obj_tag(v___x_63_))
{
case 0:
{
lean_object* v_key_64_; lean_object* v_val_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
v_key_64_ = lean_ctor_get(v___x_63_, 0);
v_val_65_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_val_65_);
lean_inc(v_key_64_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; 
lean_inc(v_key_64_);
v___x_69_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_50_, v_x_53_, v_key_64_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_del_object(v___x_67_);
lean_dec(v_val_65_);
lean_dec(v_key_64_);
lean_del_object(v___x_56_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v___x_72_; 
if (v_isShared_68_ == 0)
{
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_key_64_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_val_65_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set_tag(v___x_56_, 1);
lean_ctor_set(v___x_56_, 0, v___x_72_);
v___x_74_ = v___x_56_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
case 1:
{
lean_object* v_node_78_; size_t v___x_79_; 
lean_del_object(v___x_56_);
v_node_78_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_node_78_);
lean_dec_ref(v___x_63_);
v___x_79_ = lean_usize_shift_right(v_x_52_, v___x_59_);
v_x_51_ = v_node_78_;
v_x_52_ = v___x_79_;
goto _start;
}
default: 
{
lean_object* v___x_81_; 
lean_del_object(v___x_56_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v___x_50_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
}
}
else
{
lean_object* v_ks_83_; lean_object* v_vs_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_ks_83_ = lean_ctor_get(v_x_51_, 0);
lean_inc_ref(v_ks_83_);
v_vs_84_ = lean_ctor_get(v_x_51_, 1);
lean_inc_ref(v_vs_84_);
lean_dec_ref(v_x_51_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_50_, v_ks_83_, v_vs_84_, v___x_85_, v_x_53_);
lean_dec_ref(v_vs_84_);
lean_dec_ref(v_ks_83_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(lean_object* v___x_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
size_t v_x_5040__boxed_91_; lean_object* v_res_92_; 
v_x_5040__boxed_91_ = lean_unbox_usize(v_x_89_);
lean_dec(v_x_89_);
v_res_92_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_87_, v_x_88_, v_x_5040__boxed_91_, v_x_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(lean_object* v___x_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint64_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
lean_inc_ref(v_x_95_);
lean_inc_ref(v___x_93_);
v___x_96_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_93_, v_x_95_);
v___x_97_ = lean_uint64_to_usize(v___x_96_);
v___x_98_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_93_, v_x_94_, v___x_97_, v_x_95_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(lean_object* v_a_99_, lean_object* v_b_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_toGoalState_109_; lean_object* v_enodeMap_110_; lean_object* v_congrTable_111_; lean_object* v___x_112_; lean_object* v_key_113_; lean_object* v___x_114_; 
v___x_108_ = lean_st_ref_get(v_a_101_);
v_toGoalState_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_toGoalState_109_);
lean_dec(v___x_108_);
v_enodeMap_110_ = lean_ctor_get(v_toGoalState_109_, 2);
lean_inc_ref(v_enodeMap_110_);
v_congrTable_111_ = lean_ctor_get(v_toGoalState_109_, 5);
lean_inc_ref(v_congrTable_111_);
lean_dec_ref(v_toGoalState_109_);
v___x_112_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
v_key_113_ = l_Lean_mkAppB(v___x_112_, v_a_99_, v_b_100_);
v___x_114_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v_enodeMap_110_, v_congrTable_111_, v_key_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
else
{
lean_object* v_val_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_147_; 
v_val_117_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_147_ == 0)
{
v___x_119_ = v___x_114_;
v_isShared_120_ = v_isSharedCheck_147_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_val_117_);
lean_dec(v___x_114_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_147_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_fst_121_; lean_object* v___x_122_; 
v_fst_121_ = lean_ctor_get(v_val_117_, 0);
lean_inc(v_fst_121_);
lean_dec(v_val_117_);
lean_inc(v_fst_121_);
v___x_122_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_121_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_138_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_138_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_138_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_138_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___x_127_; 
v___x_127_ = lean_unbox(v_a_123_);
lean_dec(v_a_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_fst_121_);
lean_del_object(v___x_119_);
v___x_128_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_128_);
v___x_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v___x_133_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v_fst_121_);
v___x_133_ = v___x_119_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_fst_121_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_133_);
v___x_135_ = v___x_125_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
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
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_fst_121_);
lean_del_object(v___x_119_);
v_a_139_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_122_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_122_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(lean_object* v_a_148_, lean_object* v_b_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_148_, v_b_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f(lean_object* v_a_158_, lean_object* v_b_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_158_, v_b_159_, v_a_160_, v_a_164_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object* v_a_172_, lean_object* v_b_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_Grind_getDiseqFor_x3f(v_a_172_, v_b_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec(v_a_174_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(lean_object* v___x_186_, lean_object* v_00_u03b2_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_186_, v_x_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(lean_object* v___x_191_, lean_object* v_00_u03b2_192_, lean_object* v_x_193_, size_t v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_191_, v_x_193_, v_x_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(lean_object* v___x_197_, lean_object* v_00_u03b2_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
size_t v_x_5271__boxed_202_; lean_object* v_res_203_; 
v_x_5271__boxed_202_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_res_203_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(v___x_197_, v_00_u03b2_198_, v_x_199_, v_x_5271__boxed_202_, v_x_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(lean_object* v___x_204_, lean_object* v_00_u03b2_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_heq_208_, lean_object* v_i_209_, lean_object* v_k_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_204_, v_keys_206_, v_vals_207_, v_i_209_, v_k_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_212_, lean_object* v_00_u03b2_213_, lean_object* v_keys_214_, lean_object* v_vals_215_, lean_object* v_heq_216_, lean_object* v_i_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(v___x_212_, v_00_u03b2_213_, v_keys_214_, v_vals_215_, v_heq_216_, v_i_217_, v_k_218_);
lean_dec_ref(v_vals_215_);
lean_dec_ref(v_keys_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg(lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_220_, v_b_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
if (lean_obj_tag(v_a_230_) == 0)
{
uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = 0;
v___x_235_ = lean_box(v___x_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec_ref(v_a_230_);
v___x_239_ = 1;
v___x_240_ = lean_box(v___x_239_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_240_);
v___x_242_ = v___x_232_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_229_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_229_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg___boxed(lean_object* v_a_253_, lean_object* v_b_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_253_, v_b_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object* v_a_263_, lean_object* v_b_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_263_, v_b_264_, v_a_265_, v_a_269_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_isDiseq(v_a_277_, v_b_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
return v_res_290_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_12819__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0);
v___x_12819__overap_305_ = lean_panic_fn(v___x_304_, v_msg_292_);
v___x_306_ = lean_apply_11(v___x_12819__overap_305_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, lean_box(0));
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2));
v___x_324_ = lean_unsigned_to_nat(30u);
v___x_325_ = lean_unsigned_to_nat(44u);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1));
v___x_327_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0));
v___x_328_ = l_mkPanicMessageWithDecl(v___x_327_, v___x_326_, v___x_325_, v___x_324_, v___x_323_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object* v_a_346_, lean_object* v_b_347_, lean_object* v_eq_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___x_373_; uint8_t v___x_374_; 
lean_inc_ref(v_eq_348_);
v___x_373_ = l_Lean_Expr_cleanupAnnotations(v_eq_348_);
v___x_374_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_eq_348_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
v___y_368_ = v_a_356_;
v___y_369_ = v_a_357_;
v___y_370_ = v_a_358_;
goto v___jp_360_;
}
else
{
lean_object* v_arg_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_arg_375_ = lean_ctor_get(v___x_373_, 1);
lean_inc_ref(v_arg_375_);
v___x_376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_373_);
v___x_377_ = l_Lean_Expr_isApp(v___x_376_);
if (v___x_377_ == 0)
{
lean_dec_ref(v___x_376_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_eq_348_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
v___y_368_ = v_a_356_;
v___y_369_ = v_a_357_;
v___y_370_ = v_a_358_;
goto v___jp_360_;
}
else
{
lean_object* v_arg_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_arg_378_ = lean_ctor_get(v___x_376_, 1);
lean_inc_ref(v_arg_378_);
v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_376_);
v___x_380_ = l_Lean_Expr_isApp(v___x_379_);
if (v___x_380_ == 0)
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_eq_348_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
v___y_368_ = v_a_356_;
v___y_369_ = v_a_357_;
v___y_370_ = v_a_358_;
goto v___jp_360_;
}
else
{
lean_object* v_arg_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_arg_381_ = lean_ctor_get(v___x_379_, 1);
lean_inc_ref(v_arg_381_);
v___x_382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_379_);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_eq_348_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
v___y_368_ = v_a_356_;
v___y_369_ = v_a_357_;
v___y_370_ = v_a_358_;
goto v___jp_360_;
}
else
{
lean_object* v___x_385_; 
lean_inc(v_a_358_);
lean_inc_ref(v_a_357_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v_a_350_);
lean_inc(v_a_349_);
lean_inc_ref(v_eq_348_);
v___x_385_ = l_Lean_Meta_Grind_mkEqFalseProof(v_eq_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_460_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_460_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_460_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_460_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_u_390_; lean_object* v___y_392_; lean_object* v_h_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v_fst_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___x_440_; lean_object* v___y_442_; lean_object* v___x_456_; 
v_u_390_ = l_Lean_Expr_constLevels_x21(v___x_382_);
lean_dec_ref(v___x_382_);
v___x_440_ = l_Lean_Meta_mkOfEqFalseCore(v_eq_348_, v_a_386_);
v___x_456_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_346_, v_arg_378_, v_a_349_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; uint8_t v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v___x_458_ = lean_unbox(v_a_457_);
lean_dec(v_a_457_);
if (v___x_458_ == 0)
{
v___y_442_ = v___x_456_;
goto v___jp_441_;
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v___x_456_);
v___x_459_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_347_, v_arg_375_, v_a_349_);
v___y_442_ = v___x_459_;
goto v___jp_441_;
}
}
else
{
v___y_442_ = v___x_456_;
goto v___jp_441_;
}
v___jp_391_:
{
uint8_t v___x_404_; 
v___x_404_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_b_347_, v___y_392_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_del_object(v___x_388_);
lean_inc_ref(v___y_392_);
lean_inc_ref(v_b_347_);
v___x_405_ = lean_grind_mk_eq_proof(v_b_347_, v___y_392_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7));
v___x_411_ = l_Lean_mkConst(v___x_410_, v_u_390_);
v___x_412_ = l_Lean_mkApp6(v___x_411_, v_arg_381_, v_b_347_, v_a_346_, v___y_392_, v_a_406_, v_h_393_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_412_);
v___x_414_ = v___x_408_;
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
else
{
lean_dec_ref(v_h_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_u_390_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
return v___x_405_;
}
}
else
{
lean_object* v___x_418_; 
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_392_);
lean_dec(v_u_390_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_h_393_);
v___x_418_ = v___x_388_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_h_393_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
v___jp_420_:
{
uint8_t v___x_434_; 
v___x_434_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_346_, v_fst_421_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
lean_inc(v___y_425_);
lean_inc(v___y_424_);
lean_inc_ref(v_fst_421_);
lean_inc_ref(v_a_346_);
v___x_435_ = lean_grind_mk_eq_proof(v_a_346_, v_fst_421_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
v___x_437_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9));
lean_inc(v_u_390_);
v___x_438_ = l_Lean_mkConst(v___x_437_, v_u_390_);
lean_inc_ref(v_fst_422_);
lean_inc_ref(v_a_346_);
lean_inc_ref(v_arg_381_);
v___x_439_ = l_Lean_mkApp6(v___x_438_, v_arg_381_, v_a_346_, v_fst_421_, v_fst_422_, v_a_436_, v_snd_423_);
v___y_392_ = v_fst_422_;
v_h_393_ = v___x_439_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_426_;
v___y_397_ = v___y_427_;
v___y_398_ = v___y_428_;
v___y_399_ = v___y_429_;
v___y_400_ = v___y_430_;
v___y_401_ = v___y_431_;
v___y_402_ = v___y_432_;
v___y_403_ = v___y_433_;
goto v___jp_391_;
}
else
{
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v_snd_423_);
lean_dec_ref(v_fst_422_);
lean_dec_ref(v_fst_421_);
lean_dec(v_u_390_);
lean_del_object(v___x_388_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
return v___x_435_;
}
}
else
{
lean_dec_ref(v_fst_421_);
v___y_392_ = v_fst_422_;
v_h_393_ = v_snd_423_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_426_;
v___y_397_ = v___y_427_;
v___y_398_ = v___y_428_;
v___y_399_ = v___y_429_;
v___y_400_ = v___y_430_;
v___y_401_ = v___y_431_;
v___y_402_ = v___y_432_;
v___y_403_ = v___y_433_;
goto v___jp_391_;
}
}
v___jp_441_:
{
if (lean_obj_tag(v___y_442_) == 0)
{
lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_443_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___y_442_);
v___x_444_ = lean_unbox(v_a_443_);
lean_dec(v_a_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12));
lean_inc(v_u_390_);
v___x_446_ = l_Lean_mkConst(v___x_445_, v_u_390_);
lean_inc_ref(v_arg_375_);
lean_inc_ref(v_arg_378_);
lean_inc_ref(v_arg_381_);
v___x_447_ = l_Lean_mkApp4(v___x_446_, v_arg_381_, v_arg_378_, v_arg_375_, v___x_440_);
v_fst_421_ = v_arg_375_;
v_fst_422_ = v_arg_378_;
v_snd_423_ = v___x_447_;
v___y_424_ = v_a_349_;
v___y_425_ = v_a_350_;
v___y_426_ = v_a_351_;
v___y_427_ = v_a_352_;
v___y_428_ = v_a_353_;
v___y_429_ = v_a_354_;
v___y_430_ = v_a_355_;
v___y_431_ = v_a_356_;
v___y_432_ = v_a_357_;
v___y_433_ = v_a_358_;
goto v___jp_420_;
}
else
{
v_fst_421_ = v_arg_378_;
v_fst_422_ = v_arg_375_;
v_snd_423_ = v___x_440_;
v___y_424_ = v_a_349_;
v___y_425_ = v_a_350_;
v___y_426_ = v_a_351_;
v___y_427_ = v_a_352_;
v___y_428_ = v_a_353_;
v___y_429_ = v_a_354_;
v___y_430_ = v_a_355_;
v___y_431_ = v_a_356_;
v___y_432_ = v_a_357_;
v___y_433_ = v_a_358_;
goto v___jp_420_;
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v___x_440_);
lean_dec(v_u_390_);
lean_del_object(v___x_388_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
v_a_448_ = lean_ctor_get(v___y_442_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___y_442_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___y_442_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___y_442_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_382_);
lean_dec_ref(v_arg_381_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_eq_348_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_a_346_);
return v___x_385_;
}
}
}
}
}
v___jp_360_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3, &l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3);
v___x_372_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v___x_371_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___boxed(lean_object* v_a_461_, lean_object* v_b_462_, lean_object* v_eq_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_461_, v_b_462_, v_eq_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
lean_inc_ref(v_b_477_);
lean_inc_ref(v_a_476_);
v___x_489_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_476_, v_b_477_, v_a_478_, v_a_482_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_523_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_523_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_523_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_523_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
if (lean_obj_tag(v_a_490_) == 1)
{
lean_object* v_val_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_492_);
v_val_494_ = lean_ctor_get(v_a_490_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_518_ == 0)
{
v___x_496_ = v_a_490_;
v_isShared_497_ = v_isSharedCheck_518_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_val_494_);
lean_dec(v_a_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_518_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_476_, v_b_477_, v_val_494_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_509_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_509_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_a_499_);
v___x_504_ = v___x_496_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
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
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_496_);
v_a_510_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_498_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_498_);
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
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_a_490_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_b_477_);
lean_dec_ref(v_a_476_);
v___x_519_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_519_);
v___x_521_ = v___x_492_;
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
}
}
else
{
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_b_477_);
lean_dec_ref(v_a_476_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___boxed(lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_524_, v_b_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(lean_object* v_msgData_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v_env_545_; lean_object* v___x_546_; lean_object* v_mctx_547_; lean_object* v_lctx_548_; lean_object* v_options_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_544_ = lean_st_ref_get(v___y_542_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_env_545_);
lean_dec(v___x_544_);
v___x_546_ = lean_st_ref_get(v___y_540_);
v_mctx_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_mctx_547_);
lean_dec(v___x_546_);
v_lctx_548_ = lean_ctor_get(v___y_539_, 2);
v_options_549_ = lean_ctor_get(v___y_541_, 2);
lean_inc_ref(v_options_549_);
lean_inc_ref(v_lctx_548_);
v___x_550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_550_, 0, v_env_545_);
lean_ctor_set(v___x_550_, 1, v_mctx_547_);
lean_ctor_set(v___x_550_, 2, v_lctx_548_);
lean_ctor_set(v___x_550_, 3, v_options_549_);
v___x_551_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_msgData_538_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(lean_object* v_msgData_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msgData_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_ref_566_; lean_object* v___x_567_; lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_ref_566_ = lean_ctor_get(v___y_563_, 5);
v___x_567_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc(v_ref_566_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_ref_566_);
lean_ctor_set(v___x_572_, 1, v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 1);
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg___boxed(lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object* v_a_590_, lean_object* v_b_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; 
lean_inc(v_a_601_);
lean_inc_ref(v_a_600_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc_ref(v_b_591_);
lean_inc_ref(v_a_590_);
v___x_603_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_590_, v_b_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_620_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_620_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
if (lean_obj_tag(v_a_604_) == 1)
{
lean_object* v_val_608_; lean_object* v___x_610_; 
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_b_591_);
lean_dec_ref(v_a_590_);
v_val_608_ = lean_ctor_get(v_a_604_, 0);
lean_inc(v_val_608_);
lean_dec_ref(v_a_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_val_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_val_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_606_);
lean_dec(v_a_604_);
v___x_612_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__1, &l_Lean_Meta_Grind_mkDiseqProof___closed__1_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1);
v___x_613_ = l_Lean_indentExpr(v_a_590_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__3, &l_Lean_Meta_Grind_mkDiseqProof___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_indentExpr(v_b_591_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v___x_618_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v___x_619_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_b_591_);
lean_dec_ref(v_a_590_);
v_a_621_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_603_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_603_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof___boxed(lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_629_, v_b_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(lean_object* v_00_u03b1_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_644_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(v_00_u03b1_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
return v_res_670_;
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

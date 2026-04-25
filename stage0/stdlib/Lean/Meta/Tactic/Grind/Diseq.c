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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1;
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
lean_object* v_es_54_; lean_object* v___x_55_; size_t v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v_j_59_; lean_object* v___x_60_; 
v_es_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc_ref(v_es_54_);
lean_dec_ref(v_x_51_);
v___x_55_ = lean_box(2);
v___x_56_ = ((size_t)5ULL);
v___x_57_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1);
v___x_58_ = lean_usize_land(v_x_52_, v___x_57_);
v_j_59_ = lean_usize_to_nat(v___x_58_);
v___x_60_ = lean_array_get(v___x_55_, v_es_54_, v_j_59_);
lean_dec(v_j_59_);
lean_dec_ref(v_es_54_);
switch(lean_obj_tag(v___x_60_))
{
case 0:
{
lean_object* v_key_61_; lean_object* v_val_62_; uint8_t v___x_63_; 
v_key_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_n(v_key_61_, 2);
v_val_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_val_62_);
lean_dec_ref(v___x_60_);
v___x_63_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_50_, v_x_53_, v_key_61_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec(v_val_62_);
lean_dec(v_key_61_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_key_61_);
lean_ctor_set(v___x_65_, 1, v_val_62_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
case 1:
{
lean_object* v_node_67_; size_t v___x_68_; 
v_node_67_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_node_67_);
lean_dec_ref(v___x_60_);
v___x_68_ = lean_usize_shift_right(v_x_52_, v___x_56_);
v_x_51_ = v_node_67_;
v_x_52_ = v___x_68_;
goto _start;
}
default: 
{
lean_object* v___x_70_; 
lean_dec_ref(v_x_53_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
}
else
{
lean_object* v_ks_71_; lean_object* v_vs_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_ks_71_ = lean_ctor_get(v_x_51_, 0);
lean_inc_ref(v_ks_71_);
v_vs_72_ = lean_ctor_get(v_x_51_, 1);
lean_inc_ref(v_vs_72_);
lean_dec_ref(v_x_51_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_50_, v_ks_71_, v_vs_72_, v___x_73_, v_x_53_);
lean_dec_ref(v_vs_72_);
lean_dec_ref(v_ks_71_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(lean_object* v___x_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
size_t v_x_4773__boxed_79_; lean_object* v_res_80_; 
v_x_4773__boxed_79_ = lean_unbox_usize(v_x_77_);
lean_dec(v_x_77_);
v_res_80_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_75_, v_x_76_, v_x_4773__boxed_79_, v_x_78_);
lean_dec_ref(v___x_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(lean_object* v___x_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
uint64_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
lean_inc_ref(v_x_83_);
v___x_84_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_81_, v_x_83_);
v___x_85_ = lean_uint64_to_usize(v___x_84_);
lean_inc_ref(v_x_82_);
v___x_86_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_81_, v_x_82_, v___x_85_, v_x_83_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg___boxed(lean_object* v___x_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_87_, v_x_88_, v_x_89_);
lean_dec_ref(v_x_88_);
lean_dec_ref(v___x_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(lean_object* v_a_91_, lean_object* v_b_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v_toGoalState_101_; lean_object* v_enodeMap_102_; lean_object* v_congrTable_103_; lean_object* v___x_104_; lean_object* v_key_105_; lean_object* v___x_106_; 
v___x_100_ = lean_st_ref_get(v_a_93_);
v_toGoalState_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_toGoalState_101_);
lean_dec(v___x_100_);
v_enodeMap_102_ = lean_ctor_get(v_toGoalState_101_, 1);
lean_inc_ref(v_enodeMap_102_);
v_congrTable_103_ = lean_ctor_get(v_toGoalState_101_, 4);
lean_inc_ref(v_congrTable_103_);
lean_dec_ref(v_toGoalState_101_);
v___x_104_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
v_key_105_ = l_Lean_mkAppB(v___x_104_, v_a_91_, v_b_92_);
v___x_106_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v_enodeMap_102_, v_congrTable_103_, v_key_105_);
lean_dec_ref(v_congrTable_103_);
lean_dec_ref(v_enodeMap_102_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_139_; 
v_val_109_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_139_ == 0)
{
v___x_111_ = v___x_106_;
v_isShared_112_ = v_isSharedCheck_139_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v___x_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_139_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_fst_113_; lean_object* v___x_114_; 
v_fst_113_ = lean_ctor_get(v_val_109_, 0);
lean_inc_n(v_fst_113_, 2);
lean_dec(v_val_109_);
v___x_114_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_113_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_130_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_130_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_unbox(v_a_115_);
lean_dec(v_a_115_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_dec(v_fst_113_);
lean_del_object(v___x_111_);
v___x_120_ = lean_box(0);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_120_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
lean_object* v___x_125_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_fst_113_);
v___x_125_ = v___x_111_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_fst_113_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_125_);
v___x_127_ = v___x_117_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_fst_113_);
lean_del_object(v___x_111_);
v_a_131_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_114_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_114_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(lean_object* v_a_140_, lean_object* v_b_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_140_, v_b_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f(lean_object* v_a_150_, lean_object* v_b_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_150_, v_b_151_, v_a_152_, v_a_156_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object* v_a_164_, lean_object* v_b_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Meta_Grind_getDiseqFor_x3f(v_a_164_, v_b_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec(v_a_166_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(lean_object* v___x_178_, lean_object* v_00_u03b2_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_178_, v_x_180_, v_x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___boxed(lean_object* v___x_183_, lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(v___x_183_, v_00_u03b2_184_, v_x_185_, v_x_186_);
lean_dec_ref(v_x_185_);
lean_dec_ref(v___x_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(lean_object* v___x_188_, lean_object* v_00_u03b2_189_, lean_object* v_x_190_, size_t v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
lean_inc_ref(v_x_190_);
v___x_193_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_188_, v_x_190_, v_x_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(lean_object* v___x_194_, lean_object* v_00_u03b2_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_4938__boxed_199_; lean_object* v_res_200_; 
v_x_4938__boxed_199_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_res_200_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(v___x_194_, v_00_u03b2_195_, v_x_196_, v_x_4938__boxed_199_, v_x_198_);
lean_dec_ref(v_x_196_);
lean_dec_ref(v___x_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(lean_object* v___x_201_, lean_object* v_00_u03b2_202_, lean_object* v_keys_203_, lean_object* v_vals_204_, lean_object* v_heq_205_, lean_object* v_i_206_, lean_object* v_k_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_201_, v_keys_203_, v_vals_204_, v_i_206_, v_k_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_209_, lean_object* v_00_u03b2_210_, lean_object* v_keys_211_, lean_object* v_vals_212_, lean_object* v_heq_213_, lean_object* v_i_214_, lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(v___x_209_, v_00_u03b2_210_, v_keys_211_, v_vals_212_, v_heq_213_, v_i_214_, v_k_215_);
lean_dec_ref(v_vals_212_);
lean_dec_ref(v_keys_211_);
lean_dec_ref(v___x_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg(lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_217_, v_b_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
if (lean_obj_tag(v_a_227_) == 0)
{
uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = 0;
v___x_232_ = lean_box(v___x_231_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_232_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
else
{
uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec_ref(v_a_227_);
v___x_236_ = 1;
v___x_237_ = lean_box(v___x_236_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_237_);
v___x_239_ = v___x_229_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_226_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_226_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___redArg___boxed(lean_object* v_a_250_, lean_object* v_b_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_250_, v_b_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object* v_a_260_, lean_object* v_b_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Grind_isDiseq___redArg(v_a_260_, v_b_261_, v_a_262_, v_a_266_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Grind_isDiseq(v_a_274_, v_b_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec(v_a_276_);
return v_res_287_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_12288__overap_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0);
v___x_12288__overap_302_ = lean_panic_fn_borrowed(v___x_301_, v_msg_289_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_298_);
lean_inc(v___y_297_);
lean_inc_ref(v___y_296_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc(v___y_290_);
v___x_303_ = lean_apply_11(v___x_12288__overap_302_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, lean_box(0));
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v_msg_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec(v___y_305_);
return v_res_316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2));
v___x_321_ = lean_unsigned_to_nat(30u);
v___x_322_ = lean_unsigned_to_nat(44u);
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1));
v___x_324_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0));
v___x_325_ = l_mkPanicMessageWithDecl(v___x_324_, v___x_323_, v___x_322_, v___x_321_, v___x_320_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_eq_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_370_; uint8_t v___x_371_; 
lean_inc_ref(v_eq_345_);
v___x_370_ = l_Lean_Expr_cleanupAnnotations(v_eq_345_);
v___x_371_ = l_Lean_Expr_isApp(v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_370_);
lean_dec_ref(v_eq_345_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
goto v___jp_357_;
}
else
{
lean_object* v_arg_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_arg_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc_ref(v_arg_372_);
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_370_);
v___x_374_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_eq_345_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
goto v___jp_357_;
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
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_eq_345_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
goto v___jp_357_;
}
else
{
lean_object* v_arg_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_arg_378_ = lean_ctor_get(v___x_376_, 1);
lean_inc_ref(v_arg_378_);
v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_376_);
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1));
v___x_381_ = l_Lean_Expr_isConstOf(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_eq_345_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___y_358_ = v_a_346_;
v___y_359_ = v_a_347_;
v___y_360_ = v_a_348_;
v___y_361_ = v_a_349_;
v___y_362_ = v_a_350_;
v___y_363_ = v_a_351_;
v___y_364_ = v_a_352_;
v___y_365_ = v_a_353_;
v___y_366_ = v_a_354_;
v___y_367_ = v_a_355_;
goto v___jp_357_;
}
else
{
lean_object* v___x_382_; 
lean_inc_ref(v_eq_345_);
v___x_382_ = l_Lean_Meta_Grind_mkEqFalseProof(v_eq_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_457_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_457_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_457_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_457_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_u_387_; lean_object* v___y_389_; lean_object* v_h_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v_fst_418_; lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___x_437_; lean_object* v___y_439_; lean_object* v___x_453_; 
v_u_387_ = l_Lean_Expr_constLevels_x21(v___x_379_);
lean_dec_ref(v___x_379_);
v___x_437_ = l_Lean_Meta_mkOfEqFalseCore(v_eq_345_, v_a_383_);
v___x_453_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_343_, v_arg_375_, v_a_346_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; uint8_t v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
v___x_455_ = lean_unbox(v_a_454_);
lean_dec(v_a_454_);
if (v___x_455_ == 0)
{
v___y_439_ = v___x_453_;
goto v___jp_438_;
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v___x_453_);
v___x_456_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_344_, v_arg_372_, v_a_346_);
v___y_439_ = v___x_456_;
goto v___jp_438_;
}
}
else
{
v___y_439_ = v___x_453_;
goto v___jp_438_;
}
v___jp_388_:
{
uint8_t v___x_401_; 
v___x_401_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_b_344_, v___y_389_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_del_object(v___x_385_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_389_);
lean_inc_ref(v_b_344_);
v___x_402_ = lean_grind_mk_eq_proof(v_b_344_, v___y_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_413_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7));
v___x_408_ = l_Lean_mkConst(v___x_407_, v_u_387_);
v___x_409_ = l_Lean_mkApp6(v___x_408_, v_arg_378_, v_b_344_, v_a_343_, v___y_389_, v_a_403_, v_h_390_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_409_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_dec_ref(v_h_390_);
lean_dec_ref(v___y_389_);
lean_dec(v_u_387_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
return v___x_402_;
}
}
else
{
lean_object* v___x_415_; 
lean_dec_ref(v___y_389_);
lean_dec(v_u_387_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_h_390_);
v___x_415_ = v___x_385_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_h_390_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v___jp_417_:
{
uint8_t v___x_431_; 
v___x_431_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_343_, v_fst_418_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v_fst_418_);
lean_inc_ref(v_a_343_);
v___x_432_ = lean_grind_mk_eq_proof(v_a_343_, v_fst_418_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9));
lean_inc(v_u_387_);
v___x_435_ = l_Lean_mkConst(v___x_434_, v_u_387_);
lean_inc_ref(v_fst_419_);
lean_inc_ref(v_a_343_);
lean_inc_ref(v_arg_378_);
v___x_436_ = l_Lean_mkApp6(v___x_435_, v_arg_378_, v_a_343_, v_fst_418_, v_fst_419_, v_a_433_, v_snd_420_);
v___y_389_ = v_fst_419_;
v_h_390_ = v___x_436_;
v___y_391_ = v___y_421_;
v___y_392_ = v___y_422_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_426_;
v___y_397_ = v___y_427_;
v___y_398_ = v___y_428_;
v___y_399_ = v___y_429_;
v___y_400_ = v___y_430_;
goto v___jp_388_;
}
else
{
lean_dec_ref(v_snd_420_);
lean_dec_ref(v_fst_419_);
lean_dec_ref(v_fst_418_);
lean_dec(v_u_387_);
lean_del_object(v___x_385_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
return v___x_432_;
}
}
else
{
lean_dec_ref(v_fst_418_);
v___y_389_ = v_fst_419_;
v_h_390_ = v_snd_420_;
v___y_391_ = v___y_421_;
v___y_392_ = v___y_422_;
v___y_393_ = v___y_423_;
v___y_394_ = v___y_424_;
v___y_395_ = v___y_425_;
v___y_396_ = v___y_426_;
v___y_397_ = v___y_427_;
v___y_398_ = v___y_428_;
v___y_399_ = v___y_429_;
v___y_400_ = v___y_430_;
goto v___jp_388_;
}
}
v___jp_438_:
{
if (lean_obj_tag(v___y_439_) == 0)
{
lean_object* v_a_440_; uint8_t v___x_441_; 
v_a_440_ = lean_ctor_get(v___y_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___y_439_);
v___x_441_ = lean_unbox(v_a_440_);
lean_dec(v_a_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12));
lean_inc(v_u_387_);
v___x_443_ = l_Lean_mkConst(v___x_442_, v_u_387_);
lean_inc_ref(v_arg_372_);
lean_inc_ref(v_arg_375_);
lean_inc_ref(v_arg_378_);
v___x_444_ = l_Lean_mkApp4(v___x_443_, v_arg_378_, v_arg_375_, v_arg_372_, v___x_437_);
v_fst_418_ = v_arg_372_;
v_fst_419_ = v_arg_375_;
v_snd_420_ = v___x_444_;
v___y_421_ = v_a_346_;
v___y_422_ = v_a_347_;
v___y_423_ = v_a_348_;
v___y_424_ = v_a_349_;
v___y_425_ = v_a_350_;
v___y_426_ = v_a_351_;
v___y_427_ = v_a_352_;
v___y_428_ = v_a_353_;
v___y_429_ = v_a_354_;
v___y_430_ = v_a_355_;
goto v___jp_417_;
}
else
{
v_fst_418_ = v_arg_375_;
v_fst_419_ = v_arg_372_;
v_snd_420_ = v___x_437_;
v___y_421_ = v_a_346_;
v___y_422_ = v_a_347_;
v___y_423_ = v_a_348_;
v___y_424_ = v_a_349_;
v___y_425_ = v_a_350_;
v___y_426_ = v_a_351_;
v___y_427_ = v_a_352_;
v___y_428_ = v_a_353_;
v___y_429_ = v_a_354_;
v___y_430_ = v_a_355_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_437_);
lean_dec(v_u_387_);
lean_del_object(v___x_385_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v_a_445_ = lean_ctor_get(v___y_439_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___y_439_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___y_439_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___y_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_378_);
lean_dec_ref(v_arg_375_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_eq_345_);
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
return v___x_382_;
}
}
}
}
}
v___jp_357_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3, &l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3);
v___x_369_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(v___x_368_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing___boxed(lean_object* v_a_458_, lean_object* v_b_459_, lean_object* v_eq_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_458_, v_b_459_, v_eq_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec(v_a_461_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object* v_a_473_, lean_object* v_b_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_486_; 
lean_inc_ref(v_b_474_);
lean_inc_ref(v_a_473_);
v___x_486_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(v_a_473_, v_b_474_, v_a_475_, v_a_479_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_520_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_520_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_520_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_520_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
if (lean_obj_tag(v_a_487_) == 1)
{
lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_489_);
v_val_491_ = lean_ctor_get(v_a_487_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_515_ == 0)
{
v___x_493_ = v_a_487_;
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_dec(v_a_487_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_473_, v_b_474_, v_val_491_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_506_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_506_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_a_496_);
v___x_501_ = v___x_493_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_505_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_501_);
v___x_503_ = v___x_498_;
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
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_del_object(v___x_493_);
v_a_507_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_495_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_495_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
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
else
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v_a_487_);
lean_dec_ref(v_b_474_);
lean_dec_ref(v_a_473_);
v___x_516_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_516_);
v___x_518_ = v___x_489_;
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
else
{
lean_dec_ref(v_b_474_);
lean_dec_ref(v_a_473_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___boxed(lean_object* v_a_521_, lean_object* v_b_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_521_, v_b_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_env_542_; lean_object* v___x_543_; lean_object* v_mctx_544_; lean_object* v_lctx_545_; lean_object* v_options_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_541_ = lean_st_ref_get(v___y_539_);
v_env_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_env_542_);
lean_dec(v___x_541_);
v___x_543_ = lean_st_ref_get(v___y_537_);
v_mctx_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_ref(v_mctx_544_);
lean_dec(v___x_543_);
v_lctx_545_ = lean_ctor_get(v___y_536_, 2);
v_options_546_ = lean_ctor_get(v___y_538_, 2);
lean_inc_ref(v_options_546_);
lean_inc_ref(v_lctx_545_);
v___x_547_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_547_, 0, v_env_542_);
lean_ctor_set(v___x_547_, 1, v_mctx_544_);
lean_ctor_set(v___x_547_, 2, v_lctx_545_);
lean_ctor_set(v___x_547_, 3, v_options_546_);
v___x_548_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_msgData_535_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(lean_object* v_msgData_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msgData_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 5);
v___x_564_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_ref_563_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_ref_563_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg___boxed(lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__0));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_mkDiseqProof___closed__2));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object* v_a_587_, lean_object* v_b_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; 
lean_inc_ref(v_b_588_);
lean_inc_ref(v_a_587_);
v___x_600_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_a_587_, v_b_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_617_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_617_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
if (lean_obj_tag(v_a_601_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_607_; 
lean_dec_ref(v_b_588_);
lean_dec_ref(v_a_587_);
v_val_605_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_val_605_);
lean_dec_ref(v_a_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_val_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_val_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_del_object(v___x_603_);
lean_dec(v_a_601_);
v___x_609_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__1, &l_Lean_Meta_Grind_mkDiseqProof___closed__1_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1);
v___x_610_ = l_Lean_indentExpr(v_a_587_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_Meta_Grind_mkDiseqProof___closed__3, &l_Lean_Meta_Grind_mkDiseqProof___closed__3_once, _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Lean_indentExpr(v_b_588_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v___x_615_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_616_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_b_588_);
lean_dec_ref(v_a_587_);
v_a_618_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_600_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_600_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof___boxed(lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_626_, v_b_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec(v_a_628_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(v_msg_641_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___boxed(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(v_00_u03b1_654_, v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
return v_res_667_;
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

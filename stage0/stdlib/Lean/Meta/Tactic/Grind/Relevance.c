// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Relevance
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addNewRawFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_isRelevantAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 181, 171, 119, 158, 138, 221, 239)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 170, 199, 36, 204, 118, 150, 149)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_getRelationType_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_getRelationType_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getRelationType_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_getRelationType_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getRelationType_x3f___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isRelationOver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isRelationOver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "alreadyNorm"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__6_value),LEAN_SCALAR_PTR_LITERAL(243, 221, 60, 184, 251, 204, 208, 244)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__10_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__14_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__16_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_Relevance_collectAtoms___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_isRelevantAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_isRelevantAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getSkippedKeys(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getSkippedKeys___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_checkFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_checkFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "relevance"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(207, 56, 25, 10, 38, 56, 154, 42)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "asserting skipped fact"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7;
static const lean_ctor_object l_Lean_Meta_Grind_Relevance_registerKeys___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Relevance_registerKeys___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Relevance_registerKeys___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_registerKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_registerKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkIrrelevant_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkIrrelevant_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_skipFact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "skipping"};
static const lean_object* l_Lean_Meta_Grind_skipFact___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_skipFact___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_skipFact___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_skipFact___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_filterFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_filterFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerRelevantFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerRelevantFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Relevance"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 246, 157, 217, 11, 207, 193, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 116, 121, 69, 251, 111, 119, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 126, 233, 74, 24, 69, 53, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 44, 47, 77, 136, 233, 227, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(5, 176, 143, 250, 73, 248, 6, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 107, 244, 230, 42, 80, 202, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 23, 155, 79, 233, 232, 65, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 20, 25, 28, 196, 196, 206, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 238, 37, 64, 112, 119, 115, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 12, 14, 38, 41, 76, 250, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Grind_Relevance_collectAtoms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 50, 147, 83, 179, 206, 46, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 118, 163, 218, 206, 174, 139, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__1));
v___x_6_ = l_Lean_mkConst(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2, &l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__2);
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f___lam__0(lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3, &l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_getRelationType_x3f___lam__0___closed__3);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getRelationType_x3f___closed__21(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_Meta_Grind_getRelationType_x3f___lam__0(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f(lean_object* v_e_50_){
_start:
{
lean_object* v___y_52_; lean_object* v_val_53_; lean_object* v___y_57_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = l_Lean_Expr_cleanupAnnotations(v_e_50_);
v___x_60_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref(v___x_59_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
lean_dec_ref(v___x_59_);
v___x_63_ = l_Lean_Expr_isApp(v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v___x_62_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = l_Lean_Expr_appFnCleanup___redArg(v___x_62_);
lean_dec_ref(v___x_62_);
v___x_66_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__1));
v___x_67_ = l_Lean_Expr_isConstOf(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__3));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_65_, v___x_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Expr_isApp(v___x_65_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec_ref(v___x_65_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v_arg_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_arg_72_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_arg_72_);
v___x_73_ = l_Lean_Expr_appFnCleanup___redArg(v___x_65_);
lean_dec_ref(v___x_65_);
v___x_74_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__5));
v___x_75_ = l_Lean_Expr_isConstOf(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__7));
v___x_77_ = l_Lean_Expr_isConstOf(v___x_73_, v___x_76_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
lean_dec_ref(v_arg_72_);
v___x_78_ = l_Lean_Expr_isApp(v___x_73_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_73_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_arg_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_arg_80_ = lean_ctor_get(v___x_73_, 1);
lean_inc_ref(v_arg_80_);
v___x_81_ = l_Lean_Expr_appFnCleanup___redArg(v___x_73_);
lean_dec_ref(v___x_73_);
v___x_82_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__10));
v___x_83_ = l_Lean_Expr_isConstOf(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__13));
v___x_85_ = l_Lean_Expr_isConstOf(v___x_81_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__16));
v___x_87_ = l_Lean_Expr_isConstOf(v___x_81_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__18));
v___x_89_ = l_Lean_Expr_isConstOf(v___x_81_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__20));
v___x_91_ = l_Lean_Expr_isConstOf(v___x_81_, v___x_90_);
lean_dec_ref(v___x_81_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v_arg_80_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
lean_inc_ref(v_arg_80_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_arg_80_);
v___y_52_ = v___x_93_;
v_val_53_ = v_arg_80_;
goto v___jp_51_;
}
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_81_);
lean_inc_ref(v_arg_80_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_arg_80_);
v___y_52_ = v___x_94_;
v_val_53_ = v_arg_80_;
goto v___jp_51_;
}
}
else
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_81_);
lean_inc_ref(v_arg_80_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_arg_80_);
v___y_52_ = v___x_95_;
v_val_53_ = v_arg_80_;
goto v___jp_51_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_81_);
lean_inc_ref(v_arg_80_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v_arg_80_);
v___y_52_ = v___x_96_;
v_val_53_ = v_arg_80_;
goto v___jp_51_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_81_);
lean_inc_ref(v_arg_80_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_arg_80_);
v___y_52_ = v___x_97_;
v_val_53_ = v_arg_80_;
goto v___jp_51_;
}
}
}
else
{
lean_object* v___x_98_; 
lean_dec_ref(v___x_73_);
lean_inc_ref(v_arg_72_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_arg_72_);
v___y_52_ = v___x_98_;
v_val_53_ = v_arg_72_;
goto v___jp_51_;
}
}
else
{
lean_object* v___x_99_; 
lean_dec_ref(v___x_73_);
lean_inc_ref(v_arg_72_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v_arg_72_);
v___y_52_ = v___x_99_;
v_val_53_ = v_arg_72_;
goto v___jp_51_;
}
}
}
else
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_65_);
v___x_100_ = lean_obj_once(&l_Lean_Meta_Grind_getRelationType_x3f___closed__21, &l_Lean_Meta_Grind_getRelationType_x3f___closed__21_once, _init_l_Lean_Meta_Grind_getRelationType_x3f___closed__21);
v___y_57_ = v___x_100_;
goto v___jp_56_;
}
}
else
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_65_);
v___x_101_ = lean_obj_once(&l_Lean_Meta_Grind_getRelationType_x3f___closed__21, &l_Lean_Meta_Grind_getRelationType_x3f___closed__21_once, _init_l_Lean_Meta_Grind_getRelationType_x3f___closed__21);
v___y_57_ = v___x_101_;
goto v___jp_56_;
}
}
}
v___jp_51_:
{
uint8_t v___x_54_; 
v___x_54_ = l_Lean_Expr_hasLooseBVars(v_val_53_);
lean_dec_ref(v_val_53_);
if (v___x_54_ == 0)
{
return v___y_52_;
}
else
{
lean_object* v___x_55_; 
lean_dec(v___y_52_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
}
v___jp_56_:
{
lean_object* v_val_58_; 
v_val_58_ = lean_ctor_get(v___y_57_, 0);
lean_inc(v_val_58_);
lean_inc(v___y_57_);
v___y_52_ = v___y_57_;
v_val_53_ = v_val_58_;
goto v___jp_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getRelationType_x3f___boxed(lean_object* v_e_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Grind_getRelationType_x3f(v_e_102_);
lean_dec_ref(v_e_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isRelationOver(lean_object* v_e_104_, lean_object* v_p_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_getRelationType_x3f(v_e_104_);
if (lean_obj_tag(v___x_117_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_119_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_117_, 1);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
lean_inc(v_a_109_);
lean_inc_ref(v_a_108_);
lean_inc(v_a_107_);
lean_inc(v_a_106_);
v___x_119_ = lean_apply_12(v_p_105_, v_val_118_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_119_;
}
else
{
uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v___x_117_);
lean_dec_ref(v_p_105_);
v___x_120_ = 0;
v___x_121_ = lean_box(v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isRelationOver___boxed(lean_object* v_e_123_, lean_object* v_p_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_Grind_isRelationOver(v_e_123_, v_p_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_e_123_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms(lean_object* v_e_169_, uint8_t v_quant_170_, lean_object* v_atoms_171_){
_start:
{
lean_object* v_p_187_; lean_object* v_q_188_; 
switch(lean_obj_tag(v_e_169_))
{
case 10:
{
lean_object* v_expr_234_; 
v_expr_234_ = lean_ctor_get(v_e_169_, 1);
lean_inc_ref(v_expr_234_);
lean_dec_ref_known(v_e_169_, 2);
v_e_169_ = v_expr_234_;
goto _start;
}
case 7:
{
lean_object* v_binderType_236_; lean_object* v_body_237_; uint8_t v___x_238_; 
v_binderType_236_ = lean_ctor_get(v_e_169_, 1);
v_body_237_ = lean_ctor_get(v_e_169_, 2);
v___x_238_ = l_Lean_Expr_hasLooseBVars(v_body_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_inc_ref(v_body_237_);
lean_inc_ref(v_binderType_236_);
lean_dec_ref_known(v_e_169_, 3);
v___x_239_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_binderType_236_, v_quant_170_, v_atoms_171_);
v_e_169_ = v_body_237_;
v_atoms_171_ = v___x_239_;
goto _start;
}
else
{
if (v_quant_170_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_array_push(v_atoms_171_, v_e_169_);
return v___x_241_;
}
else
{
lean_inc_ref(v_body_237_);
lean_dec_ref_known(v_e_169_, 3);
v_e_169_ = v_body_237_;
goto _start;
}
}
}
case 8:
{
lean_object* v_value_243_; lean_object* v_body_244_; lean_object* v___x_245_; 
v_value_243_ = lean_ctor_get(v_e_169_, 2);
lean_inc_ref(v_value_243_);
v_body_244_ = lean_ctor_get(v_e_169_, 3);
lean_inc_ref(v_body_244_);
lean_dec_ref_known(v_e_169_, 4);
v___x_245_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_value_243_, v_quant_170_, v_atoms_171_);
v_e_169_ = v_body_244_;
v_atoms_171_ = v___x_245_;
goto _start;
}
case 4:
{
lean_object* v_declName_247_; 
v_declName_247_ = lean_ctor_get(v_e_169_, 0);
if (lean_obj_tag(v_declName_247_) == 1)
{
lean_object* v_pre_248_; 
v_pre_248_ = lean_ctor_get(v_declName_247_, 0);
if (lean_obj_tag(v_pre_248_) == 0)
{
lean_object* v_str_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_str_249_ = lean_ctor_get(v_declName_247_, 1);
v___x_250_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__18));
v___x_251_ = lean_string_dec_eq(v_str_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__19));
v___x_253_ = lean_string_dec_eq(v_str_249_, v___x_252_);
if (v___x_253_ == 0)
{
goto v___jp_191_;
}
else
{
lean_dec_ref_known(v_e_169_, 2);
return v_atoms_171_;
}
}
else
{
lean_dec_ref_known(v_e_169_, 2);
return v_atoms_171_;
}
}
else
{
goto v___jp_191_;
}
}
else
{
goto v___jp_191_;
}
}
default: 
{
goto v___jp_191_;
}
}
v___jp_172_:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__7));
v___x_174_ = lean_unsigned_to_nat(3u);
v___x_175_ = l_Lean_Expr_isAppOfArity(v_e_169_, v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_array_push(v_atoms_171_, v_e_169_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_177_ = l_Lean_Expr_appFn_x21(v_e_169_);
v___x_178_ = l_Lean_Expr_appFn_x21(v___x_177_);
v___x_179_ = l_Lean_Expr_appArg_x21(v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = l_Lean_Expr_isProp(v___x_179_);
lean_dec_ref(v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec_ref(v___x_177_);
v___x_181_ = lean_array_push(v_atoms_171_, v_e_169_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = l_Lean_Expr_appArg_x21(v_e_169_);
lean_dec_ref(v_e_169_);
v___x_183_ = l_Lean_Expr_appArg_x21(v___x_177_);
lean_dec_ref(v___x_177_);
v___x_184_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v___x_183_, v_quant_170_, v_atoms_171_);
v_e_169_ = v___x_182_;
v_atoms_171_ = v___x_184_;
goto _start;
}
}
}
v___jp_186_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_p_187_, v_quant_170_, v_atoms_171_);
v_e_169_ = v_q_188_;
v_atoms_171_ = v___x_189_;
goto _start;
}
v___jp_191_:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = l_Lean_Expr_cleanupAnnotations(v_e_169_);
v___x_193_ = l_Lean_Expr_isApp(v___x_192_);
if (v___x_193_ == 0)
{
lean_dec_ref(v___x_192_);
goto v___jp_172_;
}
else
{
lean_object* v_arg_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_arg_194_ = lean_ctor_get(v___x_192_, 1);
lean_inc_ref(v_arg_194_);
v___x_195_ = l_Lean_Expr_appFnCleanup___redArg(v___x_192_);
lean_dec_ref(v___x_192_);
v___x_196_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__1));
v___x_197_ = l_Lean_Expr_isConstOf(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__5));
v___x_199_ = l_Lean_Expr_isConstOf(v___x_195_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__7));
v___x_201_ = l_Lean_Expr_isConstOf(v___x_195_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = l_Lean_Expr_isApp(v___x_195_);
if (v___x_202_ == 0)
{
lean_dec_ref(v___x_195_);
lean_dec_ref(v_arg_194_);
goto v___jp_172_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = l_Lean_Expr_appFnCleanup___redArg(v___x_195_);
v___x_204_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__9));
v___x_205_ = l_Lean_Expr_isConstOf(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v_arg_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_arg_206_ = lean_ctor_get(v___x_195_, 1);
lean_inc_ref(v_arg_206_);
lean_dec_ref(v___x_195_);
v___x_207_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__11));
v___x_208_ = l_Lean_Expr_isConstOf(v___x_203_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__13));
v___x_210_ = l_Lean_Expr_isConstOf(v___x_203_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__15));
v___x_212_ = l_Lean_Expr_isConstOf(v___x_203_, v___x_211_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
v___x_213_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_arg_206_);
lean_dec_ref(v___x_203_);
lean_dec_ref(v_arg_194_);
goto v___jp_172_;
}
else
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_215_ = l_Lean_Expr_isApp(v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_206_);
lean_dec_ref(v_arg_194_);
goto v___jp_172_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_214_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_206_);
lean_dec_ref(v_arg_194_);
goto v___jp_172_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_219_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_collectAtoms___closed__17));
v___x_220_ = l_Lean_Expr_isConstOf(v___x_218_, v___x_219_);
lean_dec_ref(v___x_218_);
if (v___x_220_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_206_);
lean_dec_ref(v_arg_194_);
goto v___jp_172_;
}
else
{
lean_object* v_arg_221_; uint8_t v___x_222_; 
v_arg_221_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_arg_221_);
lean_dec_ref(v___x_216_);
v___x_222_ = l_Lean_Expr_isProp(v_arg_221_);
lean_dec_ref(v_arg_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec_ref(v___x_214_);
lean_dec_ref(v_arg_206_);
lean_dec_ref(v_arg_194_);
v___x_223_ = lean_array_push(v_atoms_171_, v_e_169_);
return v___x_223_;
}
else
{
lean_object* v_arg_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_e_169_);
v_arg_224_ = lean_ctor_get(v___x_214_, 1);
lean_inc_ref(v_arg_224_);
lean_dec_ref(v___x_214_);
v___x_225_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_arg_224_, v_quant_170_, v_atoms_171_);
v___x_226_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_arg_206_, v_quant_170_, v___x_225_);
v_e_169_ = v_arg_194_;
v_atoms_171_ = v___x_226_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v_e_169_);
v_p_187_ = v_arg_206_;
v_q_188_ = v_arg_194_;
goto v___jp_186_;
}
}
else
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v_e_169_);
v_p_187_ = v_arg_206_;
v_q_188_ = v_arg_194_;
goto v___jp_186_;
}
}
else
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v_e_169_);
v_p_187_ = v_arg_206_;
v_q_188_ = v_arg_194_;
goto v___jp_186_;
}
}
else
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v___x_195_);
if (lean_obj_tag(v_arg_194_) == 6)
{
lean_object* v_body_228_; 
lean_dec_ref(v_e_169_);
v_body_228_ = lean_ctor_get(v_arg_194_, 2);
lean_inc_ref(v_body_228_);
lean_dec_ref_known(v_arg_194_, 3);
v_e_169_ = v_body_228_;
goto _start;
}
else
{
lean_object* v___x_230_; 
lean_dec_ref(v_arg_194_);
v___x_230_ = lean_array_push(v_atoms_171_, v_e_169_);
return v___x_230_;
}
}
}
}
else
{
lean_dec_ref(v___x_195_);
lean_dec_ref(v_e_169_);
v_e_169_ = v_arg_194_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_195_);
lean_dec_ref(v_e_169_);
v_e_169_ = v_arg_194_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_195_);
lean_dec_ref(v_e_169_);
v_e_169_ = v_arg_194_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_collectAtoms___boxed(lean_object* v_e_254_, lean_object* v_quant_255_, lean_object* v_atoms_256_){
_start:
{
uint8_t v_quant_boxed_257_; lean_object* v_res_258_; 
v_quant_boxed_257_ = lean_unbox(v_quant_255_);
v_res_258_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_e_254_, v_quant_boxed_257_, v_atoms_256_);
return v_res_258_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq(lean_object* v_e_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__7));
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = l_Lean_Expr_isAppOfArity(v_e_262_, v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_266_ = l_Lean_Expr_appFn_x21(v_e_262_);
v___x_267_ = l_Lean_Expr_appFn_x21(v___x_266_);
lean_dec_ref(v___x_266_);
v___x_268_ = l_Lean_Expr_appArg_x21(v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___closed__1));
v___x_270_ = l_Lean_Expr_isConstOf(v___x_268_, v___x_269_);
lean_dec_ref(v___x_268_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq___boxed(lean_object* v_e_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq(v_e_271_);
lean_dec_ref(v_e_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0(lean_object* v_relevantSymbols_274_, uint8_t v___x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 4)
{
lean_object* v_declName_277_; uint8_t v___x_278_; 
v_declName_277_ = lean_ctor_get(v_x_276_, 0);
v___x_278_ = l_Lean_NameSet_contains(v_relevantSymbols_274_, v_declName_277_);
return v___x_278_;
}
else
{
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0___boxed(lean_object* v_relevantSymbols_279_, lean_object* v___x_280_, lean_object* v_x_281_){
_start:
{
uint8_t v___x_1913__boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v___x_1913__boxed_282_ = lean_unbox(v___x_280_);
v_res_283_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0(v_relevantSymbols_279_, v___x_1913__boxed_282_, v_x_281_);
lean_dec_ref(v_x_281_);
lean_dec(v_relevantSymbols_279_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg(lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_relevantSymbols_288_; 
v_relevantSymbols_288_ = lean_ctor_get(v_a_286_, 7);
if (lean_obj_tag(v_relevantSymbols_288_) == 0)
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___f_291_; lean_object* v___x_292_; 
v___x_289_ = 0;
v___x_290_ = lean_box(v___x_289_);
lean_inc_ref(v_relevantSymbols_288_);
v___f_291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_291_, 0, v_relevantSymbols_288_);
lean_closure_set(v___f_291_, 1, v___x_290_);
v___x_292_ = lean_find_expr(v___f_291_, v_e_285_);
lean_dec_ref(v___f_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(v___x_289_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_292_, 0);
lean_dec(v_unused_304_);
v___x_296_ = v___x_292_;
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
else
{
lean_dec(v___x_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = 1;
v___x_299_ = lean_box(v___x_298_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = 0;
v___x_306_ = lean_box(v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg___boxed(lean_object* v_e_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg(v_e_308_, v_a_309_);
lean_dec_ref(v_a_309_);
lean_dec_ref(v_e_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg(v_e_312_, v_a_315_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___boxed(lean_object* v_e_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol(v_e_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_e_325_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_isRelevantAtom(lean_object* v_e_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_isBoolEq(v_e_338_);
v___x_351_ = 1;
if (v___x_350_ == 0)
{
lean_object* v___x_352_; 
lean_inc_ref(v_e_338_);
v___x_352_ = l_Lean_Meta_Grind_Solvers_isRelevantAtom(v_e_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_a_353_);
lean_dec(v_a_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_del_object(v___x_355_);
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_containsRelevantSymbol___redArg(v_e_338_, v_a_341_);
lean_dec_ref(v_e_338_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec_ref(v_e_338_);
v___x_359_ = lean_box(v___x_351_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_359_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_dec_ref(v_e_338_);
return v___x_352_;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_e_338_);
v___x_364_ = lean_box(v___x_351_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_isRelevantAtom___boxed(lean_object* v_e_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Relevance_isRelevantAtom(v_e_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec(v_a_367_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides(lean_object* v_e_381_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = l_Lean_Expr_cleanupAnnotations(v_e_381_);
v___x_385_ = l_Lean_Expr_isApp(v___x_384_);
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_384_);
goto v___jp_382_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_384_);
v___x_387_ = l_Lean_Expr_isApp(v___x_386_);
if (v___x_387_ == 0)
{
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_384_);
goto v___jp_382_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_386_);
v___x_389_ = l_Lean_Expr_isApp(v___x_388_);
if (v___x_389_ == 0)
{
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_384_);
goto v___jp_382_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_388_);
lean_dec_ref(v___x_388_);
v___x_391_ = ((lean_object*)(l_Lean_Meta_Grind_getRelationType_x3f___closed__7));
v___x_392_ = l_Lean_Expr_isConstOf(v___x_390_, v___x_391_);
lean_dec_ref(v___x_390_);
if (v___x_392_ == 0)
{
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_384_);
goto v___jp_382_;
}
else
{
lean_object* v_arg_393_; lean_object* v___y_395_; lean_object* v_arg_403_; uint8_t v___x_404_; 
v_arg_393_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_arg_393_);
lean_dec_ref(v___x_384_);
v_arg_403_ = lean_ctor_get(v___x_386_, 1);
lean_inc_ref(v_arg_403_);
lean_dec_ref(v___x_386_);
v___x_404_ = l_Lean_Expr_isFVar(v_arg_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v_arg_403_);
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___y_395_ = v___x_405_;
goto v___jp_394_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_406_);
v___x_408_ = lean_array_push(v___x_407_, v_arg_403_);
v___y_395_ = v___x_408_;
goto v___jp_394_;
}
v___jp_394_:
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Expr_isFVar(v_arg_393_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_arg_393_);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___x_398_ = l_Array_append___redArg(v___y_395_, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_array_push(v___x_400_, v_arg_393_);
v___x_402_ = l_Array_append___redArg(v___y_395_, v___x_401_);
lean_dec_ref(v___x_401_);
return v___x_402_;
}
}
}
}
}
}
v___jp_382_:
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___boxed(lean_object* v_e_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides(v_e_409_);
lean_dec_ref(v_e_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0(lean_object* v_as_411_, size_t v_i_412_, size_t v_stop_413_, lean_object* v_b_414_){
_start:
{
lean_object* v___y_416_; uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_eq(v_i_412_, v_stop_413_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_array_uget_borrowed(v_as_411_, v_i_412_);
v___x_422_ = l_Lean_Expr_hasLooseBVars(v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_inc(v___x_421_);
v___x_423_ = lean_array_push(v_b_414_, v___x_421_);
v___x_424_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides(v___x_421_);
v___x_425_ = l_Array_append___redArg(v___x_423_, v___x_424_);
lean_dec_ref(v___x_424_);
v___y_416_ = v___x_425_;
goto v___jp_415_;
}
else
{
v___y_416_ = v_b_414_;
goto v___jp_415_;
}
}
else
{
return v_b_414_;
}
v___jp_415_:
{
size_t v___x_417_; size_t v___x_418_; 
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_412_, v___x_417_);
v_i_412_ = v___x_418_;
v_b_414_ = v___y_416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0___boxed(lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_){
_start:
{
size_t v_i_boxed_430_; size_t v_stop_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_431_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0(v_as_426_, v_i_boxed_430_, v_stop_boxed_431_, v_b_429_);
lean_dec_ref(v_as_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getSkippedKeys(lean_object* v_atoms_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___x_436_ = lean_array_get_size(v_atoms_433_);
v___x_437_ = lean_nat_dec_lt(v___x_434_, v___x_436_);
if (v___x_437_ == 0)
{
return v___x_435_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_436_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getSkippedKeys_spec__0(v_atoms_433_, v___x_438_, v___x_439_, v___x_435_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getSkippedKeys___boxed(lean_object* v_atoms_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Grind_Relevance_getSkippedKeys(v_atoms_441_);
lean_dec_ref(v_atoms_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1(lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_, lean_object* v_b_446_){
_start:
{
lean_object* v___y_448_; uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
v___x_454_ = l_Lean_Expr_hasLooseBVars(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_inc(v___x_453_);
v___x_455_ = lean_array_push(v_b_446_, v___x_453_);
v___y_448_ = v___x_455_;
goto v___jp_447_;
}
else
{
v___y_448_ = v_b_446_;
goto v___jp_447_;
}
}
else
{
return v_b_446_;
}
v___jp_447_:
{
size_t v___x_449_; size_t v___x_450_; 
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_444_, v___x_449_);
v_i_444_ = v___x_450_;
v_b_446_ = v___y_448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1___boxed(lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_stop_458_, lean_object* v_b_459_){
_start:
{
size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v_i_boxed_460_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_458_);
lean_dec(v_stop_458_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1(v_as_456_, v_i_boxed_460_, v_stop_boxed_461_, v_b_459_);
lean_dec_ref(v_as_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2(lean_object* v_as_463_, size_t v_i_464_, size_t v_stop_465_, lean_object* v_b_466_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_eq(v_i_464_, v_stop_465_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; size_t v___x_470_; size_t v___x_471_; 
v___x_468_ = lean_array_uget_borrowed(v_as_463_, v_i_464_);
lean_inc(v___x_468_);
v___x_469_ = l_Lean_collectFVars(v_b_466_, v___x_468_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_add(v_i_464_, v___x_470_);
v_i_464_ = v___x_471_;
v_b_466_ = v___x_469_;
goto _start;
}
else
{
return v_b_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2___boxed(lean_object* v_as_473_, lean_object* v_i_474_, lean_object* v_stop_475_, lean_object* v_b_476_){
_start:
{
size_t v_i_boxed_477_; size_t v_stop_boxed_478_; lean_object* v_res_479_; 
v_i_boxed_477_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_stop_boxed_478_ = lean_unbox_usize(v_stop_475_);
lean_dec(v_stop_475_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2(v_as_473_, v_i_boxed_477_, v_stop_boxed_478_, v_b_476_);
lean_dec_ref(v_as_473_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0(lean_object* v_as_480_, size_t v_i_481_, size_t v_stop_482_, lean_object* v_b_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_eq(v_i_481_, v_stop_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; 
v___x_485_ = lean_array_uget_borrowed(v_as_480_, v_i_481_);
lean_inc(v___x_485_);
v___x_486_ = l_Lean_mkFVar(v___x_485_);
v___x_487_ = lean_array_push(v_b_483_, v___x_486_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_481_, v___x_488_);
v_i_481_ = v___x_489_;
v_b_483_ = v___x_487_;
goto _start;
}
else
{
return v_b_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0___boxed(lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_){
_start:
{
size_t v_i_boxed_495_; size_t v_stop_boxed_496_; lean_object* v_res_497_; 
v_i_boxed_495_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_496_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0(v_as_491_, v_i_boxed_495_, v_stop_boxed_496_, v_b_494_);
lean_dec_ref(v_as_491_);
return v_res_497_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__0));
v___x_501_ = lean_box(1);
v___x_502_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_501_, v___x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys(lean_object* v_atoms_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___y_518_; uint8_t v___x_523_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_514_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__0));
v___x_515_ = lean_obj_once(&l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1, &l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1_once, _init_l_Lean_Meta_Grind_Relevance_getRelevantKeys___closed__1);
v___x_516_ = lean_array_get_size(v_atoms_503_);
v___x_523_ = lean_nat_dec_lt(v___x_504_, v___x_516_);
if (v___x_523_ == 0)
{
v___y_518_ = v___x_515_;
goto v___jp_517_;
}
else
{
size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((size_t)0ULL);
v___x_525_ = lean_usize_of_nat(v___x_516_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__2(v_atoms_503_, v___x_524_, v___x_525_, v___x_515_);
v___y_518_ = v___x_526_;
goto v___jp_517_;
}
v___jp_505_:
{
lean_object* v_fvarIds_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_fvarIds_508_ = lean_ctor_get(v___y_506_, 2);
lean_inc_ref(v_fvarIds_508_);
lean_dec_ref(v___y_506_);
v___x_509_ = lean_array_get_size(v_fvarIds_508_);
v___x_510_ = lean_nat_dec_lt(v___x_504_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec_ref(v_fvarIds_508_);
return v___y_507_;
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_509_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__0(v_fvarIds_508_, v___x_511_, v___x_512_, v___y_507_);
lean_dec_ref(v_fvarIds_508_);
return v___x_513_;
}
}
v___jp_517_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v___x_504_, v___x_516_);
if (v___x_519_ == 0)
{
v___y_506_ = v___y_518_;
v___y_507_ = v___x_514_;
goto v___jp_505_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_516_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_getRelevantKeys_spec__1(v_atoms_503_, v___x_520_, v___x_521_, v___x_514_);
v___y_506_ = v___y_518_;
v___y_507_ = v___x_522_;
goto v___jp_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_getRelevantKeys___boxed(lean_object* v_atoms_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_Grind_Relevance_getRelevantKeys(v_atoms_527_);
lean_dec_ref(v_atoms_527_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_529_, lean_object* v_i_530_, lean_object* v_k_531_){
_start:
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_array_get_size(v_keys_529_);
v___x_533_ = lean_nat_dec_lt(v_i_530_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v_i_530_);
return v___x_533_;
}
else
{
lean_object* v_k_x27_534_; uint8_t v___x_535_; 
v_k_x27_534_ = lean_array_fget_borrowed(v_keys_529_, v_i_530_);
v___x_535_ = lean_expr_eqv(v_k_531_, v_k_x27_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_i_530_, v___x_536_);
lean_dec(v_i_530_);
v_i_530_ = v___x_537_;
goto _start;
}
else
{
lean_dec(v_i_530_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_539_, lean_object* v_i_540_, lean_object* v_k_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg(v_keys_539_, v_i_540_, v_k_541_);
lean_dec_ref(v_k_541_);
lean_dec_ref(v_keys_539_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg(lean_object* v_x_544_, size_t v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v___x_552_; 
v_es_547_ = lean_ctor_get(v_x_544_, 0);
v___x_548_ = lean_box(2);
v___x_549_ = ((size_t)31ULL);
v___x_550_ = lean_usize_land(v_x_545_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v___x_552_ = lean_array_get_borrowed(v___x_548_, v_es_547_, v_j_551_);
lean_dec(v_j_551_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_key_553_; uint8_t v___x_554_; 
v_key_553_ = lean_ctor_get(v___x_552_, 0);
v___x_554_ = lean_expr_eqv(v_x_546_, v_key_553_);
return v___x_554_;
}
case 1:
{
lean_object* v_node_555_; size_t v___x_556_; size_t v___x_557_; 
v_node_555_ = lean_ctor_get(v___x_552_, 0);
v___x_556_ = ((size_t)5ULL);
v___x_557_ = lean_usize_shift_right(v_x_545_, v___x_556_);
v_x_544_ = v_node_555_;
v_x_545_ = v___x_557_;
goto _start;
}
default: 
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
}
}
else
{
lean_object* v_ks_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_ks_560_ = lean_ctor_get(v_x_544_, 0);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg(v_ks_560_, v___x_561_, v_x_546_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg___boxed(lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
size_t v_x_11885__boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v_x_11885__boxed_566_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_res_567_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg(v_x_563_, v_x_11885__boxed_566_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_563_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint64_t v___x_571_; size_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = l_Lean_Expr_hash(v_x_570_);
v___x_572_ = lean_uint64_to_usize(v___x_571_);
v___x_573_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg(v_x_569_, v___x_572_, v_x_570_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg___boxed(lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(v_x_574_, v_x_575_);
lean_dec_ref(v_x_575_);
lean_dec_ref(v_x_574_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2(lean_object* v___x_578_, lean_object* v_as_579_, size_t v_i_580_, size_t v_stop_581_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_eq(v_i_580_, v_stop_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_uget_borrowed(v_as_579_, v_i_580_);
v___x_584_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(v___x_578_, v___x_583_);
if (v___x_584_ == 0)
{
size_t v___x_585_; size_t v___x_586_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_580_, v___x_585_);
v_i_580_ = v___x_586_;
goto _start;
}
else
{
return v___x_584_;
}
}
else
{
uint8_t v___x_588_; 
v___x_588_ = 0;
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2___boxed(lean_object* v___x_589_, lean_object* v_as_590_, lean_object* v_i_591_, lean_object* v_stop_592_){
_start:
{
size_t v_i_boxed_593_; size_t v_stop_boxed_594_; uint8_t v_res_595_; lean_object* v_r_596_; 
v_i_boxed_593_ = lean_unbox_usize(v_i_591_);
lean_dec(v_i_591_);
v_stop_boxed_594_ = lean_unbox_usize(v_stop_592_);
lean_dec(v_stop_592_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2(v___x_589_, v_as_590_, v_i_boxed_593_, v_stop_boxed_594_);
lean_dec_ref(v_as_590_);
lean_dec_ref(v___x_589_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0(lean_object* v___x_600_, lean_object* v_as_601_, size_t v_sz_602_, size_t v_i_603_, lean_object* v_b_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_603_, v_sz_602_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v___x_600_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_b_604_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_621_; 
lean_dec_ref(v_b_604_);
v___x_618_ = lean_box(0);
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___closed__0));
v_a_620_ = lean_array_uget_borrowed(v_as_601_, v_i_603_);
lean_inc(v_a_620_);
v___x_621_ = l_Lean_Meta_Grind_Relevance_isRelevantAtom(v_a_620_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_637_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_637_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; 
v___x_626_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
if (v___x_626_ == 0)
{
size_t v___x_627_; size_t v___x_628_; 
lean_del_object(v___x_624_);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_603_, v___x_627_);
v_i_603_ = v___x_628_;
v_b_604_ = v___x_619_;
goto _start;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_630_ = lean_box(v___x_616_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_600_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_618_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_633_);
v___x_635_ = v___x_624_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v___x_600_);
v_a_638_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_621_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_621_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___boxed(lean_object* v___x_646_, lean_object* v_as_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_663_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0(v___x_646_, v_as_647_, v_sz_boxed_662_, v_i_boxed_663_, v_b_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v_as_647_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_checkFact(lean_object* v_prop_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___y_678_; uint8_t v___y_679_; lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_668_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_758_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_758_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_758_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_758_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_ematch_719_; lean_object* v_genLocal_720_; lean_object* v___x_721_; uint8_t v___y_723_; uint8_t v___x_756_; 
v_ematch_719_ = lean_ctor_get(v_a_715_, 2);
lean_inc(v_ematch_719_);
v_genLocal_720_ = lean_ctor_get(v_a_715_, 4);
lean_inc(v_genLocal_720_);
lean_dec(v_a_715_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_dec_lt(v___x_721_, v_ematch_719_);
lean_dec(v_ematch_719_);
if (v___x_756_ == 0)
{
lean_dec(v_genLocal_720_);
v___y_723_ = v___x_756_;
goto v___jp_722_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_lt(v___x_721_, v_genLocal_720_);
lean_dec(v_genLocal_720_);
v___y_723_ = v___x_757_;
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; uint8_t v___x_728_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___x_725_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_prop_665_, v___y_723_, v___x_724_);
v___x_726_ = lean_array_get_size(v___x_725_);
v___x_727_ = lean_nat_dec_eq(v___x_726_, v___x_721_);
v___x_728_ = 1;
if (v___x_727_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_729_ = lean_st_ref_get(v_a_666_);
v___x_730_ = l_Lean_Meta_Grind_Relevance_getSkippedKeys(v___x_725_);
v___x_731_ = lean_array_get_size(v___x_730_);
v___x_732_ = lean_nat_dec_lt(v___x_721_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v___x_730_);
lean_dec(v___x_729_);
lean_del_object(v___x_717_);
v___y_678_ = v___x_725_;
v___y_679_ = v___x_732_;
goto v___jp_677_;
}
else
{
lean_object* v_toGoalState_733_; lean_object* v_relevance_734_; 
v_toGoalState_733_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_toGoalState_733_);
lean_dec(v___x_729_);
v_relevance_734_ = lean_ctor_get(v_toGoalState_733_, 20);
lean_inc_ref(v_relevance_734_);
lean_dec_ref(v_toGoalState_733_);
if (v___x_732_ == 0)
{
lean_dec_ref(v_relevance_734_);
lean_dec_ref(v___x_730_);
lean_del_object(v___x_717_);
v___y_678_ = v___x_725_;
v___y_679_ = v___x_732_;
goto v___jp_677_;
}
else
{
lean_object* v_keys_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_749_; 
v_keys_735_ = lean_ctor_get(v_relevance_734_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_relevance_734_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_relevance_734_, 1);
lean_dec(v_unused_750_);
v___x_737_ = v_relevance_734_;
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_keys_735_);
lean_dec(v_relevance_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
size_t v___x_739_; size_t v___x_740_; uint8_t v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_731_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_checkFact_spec__2(v_keys_735_, v___x_730_, v___x_739_, v___x_740_);
lean_dec_ref(v___x_730_);
lean_dec_ref(v_keys_735_);
if (v___x_741_ == 0)
{
lean_del_object(v___x_737_);
lean_del_object(v___x_717_);
v___y_678_ = v___x_725_;
v___y_679_ = v___x_741_;
goto v___jp_677_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_box(v___x_728_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_725_);
lean_ctor_set(v___x_737_, 0, v___x_742_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_725_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_744_);
v___x_746_ = v___x_717_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_box(v___x_728_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_725_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_752_);
v___x_754_ = v___x_717_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_prop_665_);
v_a_759_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_714_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_714_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
v___jp_677_:
{
lean_object* v___x_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0___closed__0));
v_sz_681_ = lean_array_size(v___y_678_);
v___x_682_ = ((size_t)0ULL);
lean_inc_ref(v___y_678_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Relevance_checkFact_spec__0(v___y_678_, v___y_678_, v_sz_681_, v___x_682_, v___x_680_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_705_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_705_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_703_; 
v_fst_688_ = lean_ctor_get(v_a_684_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_a_684_, 1);
lean_dec(v_unused_704_);
v___x_690_ = v_a_684_;
v_isShared_691_ = v_isSharedCheck_703_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_fst_688_);
lean_dec(v_a_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_703_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_fst_688_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_box(v___y_679_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___y_678_);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___y_678_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_694_);
v___x_696_ = v___x_686_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; 
lean_del_object(v___x_690_);
lean_dec_ref(v___y_678_);
v_val_699_ = lean_ctor_get(v_fst_688_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_fst_688_, 1);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_val_699_);
v___x_701_ = v___x_686_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_val_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___y_678_);
v_a_706_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_683_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_683_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_checkFact___boxed(lean_object* v_prop_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Grind_Relevance_checkFact(v_prop_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec(v_a_768_);
return v_res_779_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___boxed(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1(v_00_u03b2_784_, v_x_785_, v_x_786_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___redArg(v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1___boxed(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_12242__boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_x_12242__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1(v_00_u03b2_794_, v_x_795_, v_x_12242__boxed_798_, v_x_797_);
lean_dec_ref(v_x_797_);
lean_dec_ref(v_x_795_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___redArg(v_keys_802_, v_i_805_, v_k_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_808_, lean_object* v_keys_809_, lean_object* v_vals_810_, lean_object* v_heq_811_, lean_object* v_i_812_, lean_object* v_k_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1_spec__1_spec__2(v_00_u03b2_808_, v_keys_809_, v_vals_810_, v_heq_811_, v_i_812_, v_k_813_);
lean_dec_ref(v_k_813_);
lean_dec_ref(v_vals_810_);
lean_dec_ref(v_keys_809_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10___redArg(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_845_; 
v_ks_820_ = lean_ctor_get(v_x_816_, 0);
v_vs_821_ = lean_ctor_get(v_x_816_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_845_ == 0)
{
v___x_823_ = v_x_816_;
v_isShared_824_ = v_isSharedCheck_845_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_vs_821_);
lean_inc(v_ks_820_);
lean_dec(v_x_816_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_845_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_array_get_size(v_ks_820_);
v___x_826_ = lean_nat_dec_lt(v_x_817_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_x_817_);
v___x_827_ = lean_array_push(v_ks_820_, v_x_818_);
v___x_828_ = lean_array_push(v_vs_821_, v_x_819_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_828_);
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_k_x27_832_; uint8_t v___x_833_; 
v_k_x27_832_ = lean_array_fget_borrowed(v_ks_820_, v_x_817_);
v___x_833_ = lean_expr_eqv(v_x_818_, v_k_x27_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
if (v_isShared_824_ == 0)
{
v___x_835_ = v___x_823_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_ks_820_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_vs_821_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_x_817_, v___x_836_);
lean_dec(v_x_817_);
v_x_816_ = v___x_835_;
v_x_817_ = v___x_837_;
goto _start;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_array_fset(v_ks_820_, v_x_817_, v_x_818_);
v___x_841_ = lean_array_fset(v_vs_821_, v_x_817_, v_x_819_);
lean_dec(v_x_817_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_841_);
lean_ctor_set(v___x_823_, 0, v___x_840_);
v___x_843_ = v___x_823_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1___redArg(lean_object* v_n_846_, lean_object* v_k_847_, lean_object* v_v_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10___redArg(v_n_846_, v___x_849_, v_k_847_, v_v_848_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(lean_object* v_x_852_, size_t v_x_853_, size_t v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_852_) == 0)
{
lean_object* v_es_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v_j_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_es_857_ = lean_ctor_get(v_x_852_, 0);
v___x_858_ = ((size_t)31ULL);
v___x_859_ = lean_usize_land(v_x_853_, v___x_858_);
v_j_860_ = lean_usize_to_nat(v___x_859_);
v___x_861_ = lean_array_get_size(v_es_857_);
v___x_862_ = lean_nat_dec_lt(v_j_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_dec(v_j_860_);
lean_dec(v_x_856_);
lean_dec_ref(v_x_855_);
return v_x_852_;
}
else
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_901_; 
lean_inc_ref(v_es_857_);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_852_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_x_852_, 0);
lean_dec(v_unused_902_);
v___x_864_ = v_x_852_;
v_isShared_865_ = v_isSharedCheck_901_;
goto v_resetjp_863_;
}
else
{
lean_dec(v_x_852_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_901_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_v_866_; lean_object* v___x_867_; lean_object* v_xs_x27_868_; lean_object* v___y_870_; 
v_v_866_ = lean_array_fget(v_es_857_, v_j_860_);
v___x_867_ = lean_box(0);
v_xs_x27_868_ = lean_array_fset(v_es_857_, v_j_860_, v___x_867_);
switch(lean_obj_tag(v_v_866_))
{
case 0:
{
lean_object* v_key_875_; lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_886_; 
v_key_875_ = lean_ctor_get(v_v_866_, 0);
v_val_876_ = lean_ctor_get(v_v_866_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_v_866_);
if (v_isSharedCheck_886_ == 0)
{
v___x_878_ = v_v_866_;
v_isShared_879_ = v_isSharedCheck_886_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_inc(v_key_875_);
lean_dec(v_v_866_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_886_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v___x_880_; 
v___x_880_ = lean_expr_eqv(v_x_855_, v_key_875_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_del_object(v___x_878_);
v___x_881_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_875_, v_val_876_, v_x_855_, v_x_856_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___y_870_ = v___x_882_;
goto v___jp_869_;
}
else
{
lean_object* v___x_884_; 
lean_dec(v_val_876_);
lean_dec(v_key_875_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v_x_856_);
lean_ctor_set(v___x_878_, 0, v_x_855_);
v___x_884_ = v___x_878_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_x_855_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_x_856_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v___y_870_ = v___x_884_;
goto v___jp_869_;
}
}
}
}
case 1:
{
lean_object* v_node_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_node_887_ = lean_ctor_get(v_v_866_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_v_866_);
if (v_isSharedCheck_899_ == 0)
{
v___x_889_ = v_v_866_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_node_887_);
lean_dec(v_v_866_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_891_ = ((size_t)5ULL);
v___x_892_ = lean_usize_shift_right(v_x_853_, v___x_891_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_x_854_, v___x_893_);
v___x_895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(v_node_887_, v___x_892_, v___x_894_, v_x_855_, v_x_856_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_895_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
v___y_870_ = v___x_897_;
goto v___jp_869_;
}
}
}
default: 
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_x_855_);
lean_ctor_set(v___x_900_, 1, v_x_856_);
v___y_870_ = v___x_900_;
goto v___jp_869_;
}
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_array_fset(v_xs_x27_868_, v_j_860_, v___y_870_);
lean_dec(v_j_860_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_871_);
v___x_873_ = v___x_864_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
else
{
lean_object* v_ks_903_; lean_object* v_vs_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_922_; 
v_ks_903_ = lean_ctor_get(v_x_852_, 0);
v_vs_904_ = lean_ctor_get(v_x_852_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_852_);
if (v_isSharedCheck_922_ == 0)
{
v___x_906_ = v_x_852_;
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_vs_904_);
lean_inc(v_ks_903_);
lean_dec(v_x_852_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_ks_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_vs_904_);
v___x_909_ = v_reuseFailAlloc_921_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v_newNode_910_; size_t v___x_911_; uint8_t v___x_912_; 
v_newNode_910_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1___redArg(v___x_909_, v_x_855_, v_x_856_);
v___x_911_ = ((size_t)7ULL);
v___x_912_ = lean_usize_dec_le(v___x_911_, v_x_854_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_910_);
v___x_914_ = lean_unsigned_to_nat(4u);
v___x_915_ = lean_nat_dec_lt(v___x_913_, v___x_914_);
lean_dec(v___x_913_);
if (v___x_915_ == 0)
{
lean_object* v_ks_916_; lean_object* v_vs_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_ks_916_ = lean_ctor_get(v_newNode_910_, 0);
lean_inc_ref(v_ks_916_);
v_vs_917_ = lean_ctor_get(v_newNode_910_, 1);
lean_inc_ref(v_vs_917_);
lean_dec_ref(v_newNode_910_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___closed__0);
v___x_920_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg(v_x_854_, v_ks_916_, v_vs_917_, v___x_918_, v___x_919_);
lean_dec_ref(v_vs_917_);
lean_dec_ref(v_ks_916_);
return v___x_920_;
}
else
{
return v_newNode_910_;
}
}
else
{
return v_newNode_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg(size_t v_depth_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_i_926_, lean_object* v_entries_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_keys_924_);
v___x_929_ = lean_nat_dec_lt(v_i_926_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec(v_i_926_);
return v_entries_927_;
}
else
{
lean_object* v_k_930_; lean_object* v_v_931_; uint64_t v___x_932_; size_t v_h_933_; size_t v___x_934_; lean_object* v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v_h_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_k_930_ = lean_array_fget_borrowed(v_keys_924_, v_i_926_);
v_v_931_ = lean_array_fget_borrowed(v_vals_925_, v_i_926_);
v___x_932_ = l_Lean_Expr_hash(v_k_930_);
v_h_933_ = lean_uint64_to_usize(v___x_932_);
v___x_934_ = ((size_t)5ULL);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_sub(v_depth_923_, v___x_936_);
v___x_938_ = lean_usize_mul(v___x_934_, v___x_937_);
v_h_939_ = lean_usize_shift_right(v_h_933_, v___x_938_);
v___x_940_ = lean_nat_add(v_i_926_, v___x_935_);
lean_dec(v_i_926_);
lean_inc(v_v_931_);
lean_inc(v_k_930_);
v___x_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(v_entries_927_, v_h_939_, v_depth_923_, v_k_930_, v_v_931_);
v_i_926_ = v___x_940_;
v_entries_927_ = v___x_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_943_, lean_object* v_keys_944_, lean_object* v_vals_945_, lean_object* v_i_946_, lean_object* v_entries_947_){
_start:
{
size_t v_depth_boxed_948_; lean_object* v_res_949_; 
v_depth_boxed_948_ = lean_unbox_usize(v_depth_943_);
lean_dec(v_depth_943_);
v_res_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg(v_depth_boxed_948_, v_keys_944_, v_vals_945_, v_i_946_, v_entries_947_);
lean_dec_ref(v_vals_945_);
lean_dec_ref(v_keys_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg___boxed(lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_32553__boxed_955_; size_t v_x_32554__boxed_956_; lean_object* v_res_957_; 
v_x_32553__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_x_32554__boxed_956_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(v_x_950_, v_x_32553__boxed_955_, v_x_32554__boxed_956_, v_x_953_, v_x_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0___redArg(lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
uint64_t v___x_961_; size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_961_ = l_Lean_Expr_hash(v_x_959_);
v___x_962_ = lean_uint64_to_usize(v___x_961_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(v_x_958_, v___x_962_, v___x_963_, v_x_959_, v_x_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6(lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_, lean_object* v_b_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; size_t v___x_973_; size_t v___x_974_; 
v___x_970_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
v___x_971_ = lean_box(0);
lean_inc(v___x_970_);
v___x_972_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0___redArg(v_b_968_, v___x_970_, v___x_971_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_966_, v___x_973_);
v_i_966_ = v___x_974_;
v_b_968_ = v___x_972_;
goto _start;
}
else
{
return v_b_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6___boxed(lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_, lean_object* v_b_979_){
_start:
{
size_t v_i_boxed_980_; size_t v_stop_boxed_981_; lean_object* v_res_982_; 
v_i_boxed_980_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_981_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6(v_as_976_, v_i_boxed_980_, v_stop_boxed_981_, v_b_979_);
lean_dec_ref(v_as_976_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2(lean_object* v_a_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
v___x_989_ = lean_expr_eqv(v_a_983_, v___x_988_);
if (v___x_989_ == 0)
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_985_, v___x_990_);
v_i_985_ = v___x_991_;
goto _start;
}
else
{
return v___x_989_;
}
}
else
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2___boxed(lean_object* v_a_994_, lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_stop_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_997_);
lean_dec(v_stop_997_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2(v_a_994_, v_as_995_, v_i_boxed_998_, v_stop_boxed_999_);
lean_dec_ref(v_as_995_);
lean_dec_ref(v_a_994_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1(lean_object* v_as_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_as_1002_);
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
return v___x_1006_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1005_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1_spec__2(v_a_1003_, v_as_1002_, v___x_1007_, v___x_1008_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1___boxed(lean_object* v_as_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1(v_as_1010_, v_a_1011_);
lean_dec_ref(v_a_1011_);
lean_dec_ref(v_as_1010_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2(lean_object* v___y_1014_, lean_object* v_as_1015_, size_t v_i_1016_, size_t v_stop_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_usize_dec_eq(v_i_1016_, v_stop_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_array_uget_borrowed(v_as_1015_, v_i_1016_);
v___x_1020_ = l_Array_contains___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__1(v___y_1014_, v___x_1019_);
if (v___x_1020_ == 0)
{
size_t v___x_1021_; size_t v___x_1022_; 
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_1016_, v___x_1021_);
v_i_1016_ = v___x_1022_;
goto _start;
}
else
{
return v___x_1020_;
}
}
else
{
uint8_t v___x_1024_; 
v___x_1024_ = 0;
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2___boxed(lean_object* v___y_1025_, lean_object* v_as_1026_, lean_object* v_i_1027_, lean_object* v_stop_1028_){
_start:
{
size_t v_i_boxed_1029_; size_t v_stop_boxed_1030_; uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_i_boxed_1029_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_stop_boxed_1030_ = lean_unbox_usize(v_stop_1028_);
lean_dec(v_stop_1028_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2(v___y_1025_, v_as_1026_, v_i_boxed_1029_, v_stop_boxed_1030_);
lean_dec_ref(v_as_1026_);
lean_dec_ref(v___y_1025_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3(lean_object* v___y_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1046_; 
v_fst_1036_ = lean_ctor_get(v_a_1035_, 0);
v_snd_1037_ = lean_ctor_get(v_a_1035_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1039_ = v_a_1035_;
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snd_1037_);
lean_inc(v_fst_1036_);
lean_dec(v_a_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = l_List_reverse___redArg(v_fst_1036_);
v___x_1042_ = l_List_reverse___redArg(v_snd_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___x_1042_);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1044_ = v___x_1039_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_object* v_head_1047_; lean_object* v_tail_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1076_; 
v_head_1047_ = lean_ctor_get(v_a_1034_, 0);
v_tail_1048_ = lean_ctor_get(v_a_1034_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1050_ = v_a_1034_;
v_isShared_1051_ = v_isSharedCheck_1076_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_tail_1048_);
lean_inc(v_head_1047_);
lean_dec(v_a_1034_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1076_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1075_; 
v_fst_1052_ = lean_ctor_get(v_a_1035_, 0);
v_snd_1053_ = lean_ctor_get(v_a_1035_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1055_ = v_a_1035_;
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v_a_1035_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_keys_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_keys_1065_ = lean_ctor_get(v_head_1047_, 4);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_array_get_size(v_keys_1065_);
v___x_1068_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
goto v___jp_1057_;
}
else
{
if (v___x_1068_ == 0)
{
goto v___jp_1057_;
}
else
{
size_t v___x_1069_; size_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = lean_usize_of_nat(v___x_1067_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__2(v___y_1033_, v_keys_1065_, v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
goto v___jp_1057_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1055_);
lean_del_object(v___x_1050_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_head_1047_);
lean_ctor_set(v___x_1072_, 1, v_fst_1052_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_snd_1053_);
v_a_1034_ = v_tail_1048_;
v_a_1035_ = v___x_1073_;
goto _start;
}
}
}
v___jp_1057_:
{
lean_object* v___x_1059_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_snd_1053_);
v___x_1059_ = v___x_1050_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_head_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_snd_1053_);
v___x_1059_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1059_);
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_fst_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v_a_1034_ = v_tail_1048_;
v_a_1035_ = v___x_1061_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3___boxed(lean_object* v___y_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3(v___y_1077_, v_a_1078_, v_a_1079_);
lean_dec_ref(v___y_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6(lean_object* v_msgData_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_env_1088_; uint8_t v___x_1089_; lean_object* v_env_1090_; lean_object* v___x_1091_; lean_object* v_toCold_1092_; lean_object* v_mctx_1093_; lean_object* v_lctx_1094_; lean_object* v_options_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
v_env_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_env_1088_);
lean_dec(v___x_1087_);
v___x_1089_ = 0;
v_env_1090_ = l_Lean_Environment_setRecordingDeps(v_env_1088_, v___x_1089_);
v___x_1091_ = lean_st_ref_get(v___y_1083_);
v_toCold_1092_ = lean_ctor_get(v___y_1084_, 0);
v_mctx_1093_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_mctx_1093_);
lean_dec(v___x_1091_);
v_lctx_1094_ = lean_ctor_get(v___y_1082_, 2);
v_options_1095_ = lean_ctor_get(v_toCold_1092_, 2);
lean_inc_ref(v_options_1095_);
lean_inc_ref(v_lctx_1094_);
v___x_1096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1096_, 0, v_env_1090_);
lean_ctor_set(v___x_1096_, 1, v_mctx_1093_);
lean_ctor_set(v___x_1096_, 2, v_lctx_1094_);
lean_ctor_set(v___x_1096_, 3, v_options_1095_);
v___x_1097_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v_msgData_1081_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6___boxed(lean_object* v_msgData_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6(v_msgData_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1105_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1106_; double v___x_1107_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_float_of_nat(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(lean_object* v_cls_1111_, lean_object* v_msg_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_ref_1118_; lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1165_; 
v_ref_1118_ = lean_ctor_get(v___y_1115_, 2);
v___x_1119_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4_spec__6(v_msg_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1165_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1165_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v_traceState_1125_; lean_object* v_env_1126_; lean_object* v_nextMacroScope_1127_; lean_object* v_ngen_1128_; lean_object* v_auxDeclNGen_1129_; lean_object* v_cache_1130_; lean_object* v_recordedDeps_1131_; lean_object* v_messages_1132_; lean_object* v_infoState_1133_; lean_object* v_snapshotTasks_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1164_; 
v___x_1124_ = lean_st_ref_take(v___y_1116_);
v_traceState_1125_ = lean_ctor_get(v___x_1124_, 4);
v_env_1126_ = lean_ctor_get(v___x_1124_, 0);
v_nextMacroScope_1127_ = lean_ctor_get(v___x_1124_, 1);
v_ngen_1128_ = lean_ctor_get(v___x_1124_, 2);
v_auxDeclNGen_1129_ = lean_ctor_get(v___x_1124_, 3);
v_cache_1130_ = lean_ctor_get(v___x_1124_, 5);
v_recordedDeps_1131_ = lean_ctor_get(v___x_1124_, 6);
v_messages_1132_ = lean_ctor_get(v___x_1124_, 7);
v_infoState_1133_ = lean_ctor_get(v___x_1124_, 8);
v_snapshotTasks_1134_ = lean_ctor_get(v___x_1124_, 9);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1164_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snapshotTasks_1134_);
lean_inc(v_infoState_1133_);
lean_inc(v_messages_1132_);
lean_inc(v_recordedDeps_1131_);
lean_inc(v_cache_1130_);
lean_inc(v_traceState_1125_);
lean_inc(v_auxDeclNGen_1129_);
lean_inc(v_ngen_1128_);
lean_inc(v_nextMacroScope_1127_);
lean_inc(v_env_1126_);
lean_dec(v___x_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1164_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
uint64_t v_tid_1138_; lean_object* v_traces_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1163_; 
v_tid_1138_ = lean_ctor_get_uint64(v_traceState_1125_, sizeof(void*)*1);
v_traces_1139_ = lean_ctor_get(v_traceState_1125_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_traceState_1125_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1141_ = v_traceState_1125_;
v_isShared_1142_ = v_isSharedCheck_1163_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_traces_1139_);
lean_dec(v_traceState_1125_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1163_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; double v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__0);
v___x_1146_ = 0;
v___x_1147_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__1));
v___x_1148_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1148_, 0, v_cls_1111_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
lean_ctor_set_float(v___x_1148_, sizeof(void*)*3, v___x_1145_);
lean_ctor_set_float(v___x_1148_, sizeof(void*)*3 + 8, v___x_1145_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*3 + 16, v___x_1146_);
v___x_1149_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___closed__2));
v___x_1150_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v_a_1120_);
lean_ctor_set(v___x_1150_, 2, v___x_1149_);
lean_inc(v_ref_1118_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_ref_1118_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_PersistentArray_push___redArg(v_traces_1139_, v___x_1151_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1152_);
v___x_1154_ = v___x_1141_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1152_);
lean_ctor_set_uint64(v_reuseFailAlloc_1162_, sizeof(void*)*1, v_tid_1138_);
v___x_1154_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 4, v___x_1154_);
v___x_1156_ = v___x_1136_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_env_1126_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_nextMacroScope_1127_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_ngen_1128_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_auxDeclNGen_1129_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_cache_1130_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_recordedDeps_1131_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v_messages_1132_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_infoState_1133_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v_snapshotTasks_1134_);
v___x_1156_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_st_ref_put(v___y_1116_, v___x_1156_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1143_);
v___x_1159_ = v___x_1122_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1143_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg___boxed(lean_object* v_cls_1166_, lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(v_cls_1166_, v_msg_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7(lean_object* v___x_1174_, lean_object* v_as_1175_, size_t v_i_1176_, size_t v_stop_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v___y_1180_; uint8_t v___x_1184_; 
v___x_1184_ = lean_usize_dec_eq(v_i_1176_, v_stop_1177_);
if (v___x_1184_ == 0)
{
lean_object* v_keys_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_keys_1185_ = lean_ctor_get(v___x_1174_, 0);
v___x_1186_ = lean_array_uget_borrowed(v_as_1175_, v_i_1176_);
v___x_1187_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Relevance_checkFact_spec__1___redArg(v_keys_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_inc(v___x_1186_);
v___x_1188_ = lean_array_push(v_b_1178_, v___x_1186_);
v___y_1180_ = v___x_1188_;
goto v___jp_1179_;
}
else
{
v___y_1180_ = v_b_1178_;
goto v___jp_1179_;
}
}
else
{
return v_b_1178_;
}
v___jp_1179_:
{
size_t v___x_1181_; size_t v___x_1182_; 
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1176_, v___x_1181_);
v_i_1176_ = v___x_1182_;
v_b_1178_ = v___y_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7___boxed(lean_object* v___x_1189_, lean_object* v_as_1190_, lean_object* v_i_1191_, lean_object* v_stop_1192_, lean_object* v_b_1193_){
_start:
{
size_t v_i_boxed_1194_; size_t v_stop_boxed_1195_; lean_object* v_res_1196_; 
v_i_boxed_1194_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_stop_boxed_1195_ = lean_unbox_usize(v_stop_1192_);
lean_dec(v_stop_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7(v___x_1189_, v_as_1190_, v_i_boxed_1194_, v_stop_boxed_1195_, v_b_1193_);
lean_dec_ref(v_as_1190_);
lean_dec_ref(v___x_1189_);
return v_res_1196_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2));
v___x_1206_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__4));
v___x_1207_ = l_Lean_Name_append(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__6));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_registerKeys(lean_object* v_keys_1213_, lean_object* v_generation_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_toGoalState_1227_; lean_object* v_relevance_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___x_1358_; lean_object* v___y_1360_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1226_ = lean_st_ref_get(v_a_1215_);
v_toGoalState_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_toGoalState_1227_);
lean_dec(v___x_1226_);
v_relevance_1228_ = lean_ctor_get(v_toGoalState_1227_, 20);
lean_inc_ref(v_relevance_1228_);
lean_dec_ref(v_toGoalState_1227_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_keys_1213_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___x_1372_ = lean_nat_dec_lt(v___x_1358_, v___x_1370_);
if (v___x_1372_ == 0)
{
v___y_1360_ = v___x_1371_;
goto v___jp_1359_;
}
else
{
size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = lean_usize_of_nat(v___x_1370_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__7(v_relevance_1228_, v_keys_1213_, v___x_1373_, v___x_1374_, v___x_1371_);
v___y_1360_ = v___x_1375_;
goto v___jp_1359_;
}
v___jp_1229_:
{
lean_object* v___x_1232_; lean_object* v_toGoalState_1233_; lean_object* v_relevance_1234_; lean_object* v_mvarId_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1356_; 
v___x_1232_ = lean_st_ref_take(v_a_1215_);
v_toGoalState_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_toGoalState_1233_);
v_relevance_1234_ = lean_ctor_get(v_toGoalState_1233_, 20);
lean_inc_ref(v_relevance_1234_);
v_mvarId_1235_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1357_);
v___x_1237_ = v___x_1232_;
v_isShared_1238_ = v_isSharedCheck_1356_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_mvarId_1235_);
lean_dec(v___x_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1356_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_nextDeclIdx_1239_; lean_object* v_enodeMap_1240_; lean_object* v_exprs_1241_; lean_object* v_parents_1242_; lean_object* v_congrTable_1243_; lean_object* v_appMap_1244_; lean_object* v_indicesFound_1245_; lean_object* v_toProcess_1246_; lean_object* v_internalizing_1247_; uint8_t v_inconsistent_1248_; lean_object* v_nextIdx_1249_; lean_object* v_newRawFacts_1250_; lean_object* v_facts_1251_; lean_object* v_extThms_1252_; lean_object* v_ematch_1253_; lean_object* v_inj_1254_; lean_object* v_split_1255_; lean_object* v_clean_1256_; lean_object* v_sstates_1257_; lean_object* v_goalStack_1258_; uint64_t v_introBase_1259_; lean_object* v_numIntros_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1354_; 
v_nextDeclIdx_1239_ = lean_ctor_get(v_toGoalState_1233_, 0);
v_enodeMap_1240_ = lean_ctor_get(v_toGoalState_1233_, 1);
v_exprs_1241_ = lean_ctor_get(v_toGoalState_1233_, 2);
v_parents_1242_ = lean_ctor_get(v_toGoalState_1233_, 3);
v_congrTable_1243_ = lean_ctor_get(v_toGoalState_1233_, 4);
v_appMap_1244_ = lean_ctor_get(v_toGoalState_1233_, 5);
v_indicesFound_1245_ = lean_ctor_get(v_toGoalState_1233_, 6);
v_toProcess_1246_ = lean_ctor_get(v_toGoalState_1233_, 7);
v_internalizing_1247_ = lean_ctor_get(v_toGoalState_1233_, 8);
v_inconsistent_1248_ = lean_ctor_get_uint8(v_toGoalState_1233_, sizeof(void*)*21 + 8);
v_nextIdx_1249_ = lean_ctor_get(v_toGoalState_1233_, 9);
v_newRawFacts_1250_ = lean_ctor_get(v_toGoalState_1233_, 10);
v_facts_1251_ = lean_ctor_get(v_toGoalState_1233_, 11);
v_extThms_1252_ = lean_ctor_get(v_toGoalState_1233_, 12);
v_ematch_1253_ = lean_ctor_get(v_toGoalState_1233_, 13);
v_inj_1254_ = lean_ctor_get(v_toGoalState_1233_, 14);
v_split_1255_ = lean_ctor_get(v_toGoalState_1233_, 15);
v_clean_1256_ = lean_ctor_get(v_toGoalState_1233_, 16);
v_sstates_1257_ = lean_ctor_get(v_toGoalState_1233_, 17);
v_goalStack_1258_ = lean_ctor_get(v_toGoalState_1233_, 18);
v_introBase_1259_ = lean_ctor_get_uint64(v_toGoalState_1233_, sizeof(void*)*21);
v_numIntros_1260_ = lean_ctor_get(v_toGoalState_1233_, 19);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_toGoalState_1233_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_toGoalState_1233_, 20);
lean_dec(v_unused_1355_);
v___x_1262_ = v_toGoalState_1233_;
v_isShared_1263_ = v_isSharedCheck_1354_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_numIntros_1260_);
lean_inc(v_goalStack_1258_);
lean_inc(v_sstates_1257_);
lean_inc(v_clean_1256_);
lean_inc(v_split_1255_);
lean_inc(v_inj_1254_);
lean_inc(v_ematch_1253_);
lean_inc(v_extThms_1252_);
lean_inc(v_facts_1251_);
lean_inc(v_newRawFacts_1250_);
lean_inc(v_nextIdx_1249_);
lean_inc(v_internalizing_1247_);
lean_inc(v_toProcess_1246_);
lean_inc(v_indicesFound_1245_);
lean_inc(v_appMap_1244_);
lean_inc(v_congrTable_1243_);
lean_inc(v_parents_1242_);
lean_inc(v_exprs_1241_);
lean_inc(v_enodeMap_1240_);
lean_inc(v_nextDeclIdx_1239_);
lean_dec(v_toGoalState_1233_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1354_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_skipped_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1352_; 
v_skipped_1264_ = lean_ctor_get(v_relevance_1234_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_relevance_1234_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_relevance_1234_, 0);
lean_dec(v_unused_1353_);
v___x_1266_ = v_relevance_1234_;
v_isShared_1267_ = v_isSharedCheck_1352_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_skipped_1264_);
lean_dec(v_relevance_1234_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1352_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___y_1231_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___y_1231_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_skipped_1264_);
v___x_1269_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 20, v___x_1269_);
v___x_1271_ = v___x_1262_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_nextDeclIdx_1239_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_enodeMap_1240_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_exprs_1241_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_parents_1242_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_congrTable_1243_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_appMap_1244_);
lean_ctor_set(v_reuseFailAlloc_1350_, 6, v_indicesFound_1245_);
lean_ctor_set(v_reuseFailAlloc_1350_, 7, v_toProcess_1246_);
lean_ctor_set(v_reuseFailAlloc_1350_, 8, v_internalizing_1247_);
lean_ctor_set(v_reuseFailAlloc_1350_, 9, v_nextIdx_1249_);
lean_ctor_set(v_reuseFailAlloc_1350_, 10, v_newRawFacts_1250_);
lean_ctor_set(v_reuseFailAlloc_1350_, 11, v_facts_1251_);
lean_ctor_set(v_reuseFailAlloc_1350_, 12, v_extThms_1252_);
lean_ctor_set(v_reuseFailAlloc_1350_, 13, v_ematch_1253_);
lean_ctor_set(v_reuseFailAlloc_1350_, 14, v_inj_1254_);
lean_ctor_set(v_reuseFailAlloc_1350_, 15, v_split_1255_);
lean_ctor_set(v_reuseFailAlloc_1350_, 16, v_clean_1256_);
lean_ctor_set(v_reuseFailAlloc_1350_, 17, v_sstates_1257_);
lean_ctor_set(v_reuseFailAlloc_1350_, 18, v_goalStack_1258_);
lean_ctor_set(v_reuseFailAlloc_1350_, 19, v_numIntros_1260_);
lean_ctor_set(v_reuseFailAlloc_1350_, 20, v___x_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*21 + 8, v_inconsistent_1248_);
lean_ctor_set_uint64(v_reuseFailAlloc_1350_, sizeof(void*)*21, v_introBase_1259_);
v___x_1271_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1271_);
v___x_1273_ = v___x_1237_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_mvarId_1235_);
v___x_1273_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v_skipped_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_st_ref_put(v_a_1215_, v___x_1273_);
v_skipped_1275_ = lean_ctor_get(v_relevance_1228_, 1);
lean_inc(v_skipped_1275_);
lean_dec_ref(v_relevance_1228_);
v___x_1276_ = l_List_isEmpty___redArg(v_skipped_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_fst_1279_; lean_object* v_snd_1280_; uint8_t v___x_1281_; 
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Grind_Relevance_registerKeys___closed__0));
v___x_1278_ = l_List_partition_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__3(v___y_1230_, v_skipped_1275_, v___x_1277_);
lean_dec_ref(v___y_1230_);
v_fst_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_fst_1279_);
v_snd_1280_ = lean_ctor_get(v___x_1278_, 1);
lean_inc(v_snd_1280_);
lean_dec_ref(v___x_1278_);
v___x_1281_ = l_List_isEmpty___redArg(v_fst_1279_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v_toGoalState_1283_; lean_object* v_relevance_1284_; lean_object* v_mvarId_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1343_; 
v___x_1282_ = lean_st_ref_take(v_a_1215_);
v_toGoalState_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_toGoalState_1283_);
v_relevance_1284_ = lean_ctor_get(v_toGoalState_1283_, 20);
lean_inc_ref(v_relevance_1284_);
v_mvarId_1285_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1282_, 0);
lean_dec(v_unused_1344_);
v___x_1287_ = v___x_1282_;
v_isShared_1288_ = v_isSharedCheck_1343_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_mvarId_1285_);
lean_dec(v___x_1282_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1343_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_nextDeclIdx_1289_; lean_object* v_enodeMap_1290_; lean_object* v_exprs_1291_; lean_object* v_parents_1292_; lean_object* v_congrTable_1293_; lean_object* v_appMap_1294_; lean_object* v_indicesFound_1295_; lean_object* v_toProcess_1296_; lean_object* v_internalizing_1297_; uint8_t v_inconsistent_1298_; lean_object* v_nextIdx_1299_; lean_object* v_newRawFacts_1300_; lean_object* v_facts_1301_; lean_object* v_extThms_1302_; lean_object* v_ematch_1303_; lean_object* v_inj_1304_; lean_object* v_split_1305_; lean_object* v_clean_1306_; lean_object* v_sstates_1307_; lean_object* v_goalStack_1308_; uint64_t v_introBase_1309_; lean_object* v_numIntros_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1341_; 
v_nextDeclIdx_1289_ = lean_ctor_get(v_toGoalState_1283_, 0);
v_enodeMap_1290_ = lean_ctor_get(v_toGoalState_1283_, 1);
v_exprs_1291_ = lean_ctor_get(v_toGoalState_1283_, 2);
v_parents_1292_ = lean_ctor_get(v_toGoalState_1283_, 3);
v_congrTable_1293_ = lean_ctor_get(v_toGoalState_1283_, 4);
v_appMap_1294_ = lean_ctor_get(v_toGoalState_1283_, 5);
v_indicesFound_1295_ = lean_ctor_get(v_toGoalState_1283_, 6);
v_toProcess_1296_ = lean_ctor_get(v_toGoalState_1283_, 7);
v_internalizing_1297_ = lean_ctor_get(v_toGoalState_1283_, 8);
v_inconsistent_1298_ = lean_ctor_get_uint8(v_toGoalState_1283_, sizeof(void*)*21 + 8);
v_nextIdx_1299_ = lean_ctor_get(v_toGoalState_1283_, 9);
v_newRawFacts_1300_ = lean_ctor_get(v_toGoalState_1283_, 10);
v_facts_1301_ = lean_ctor_get(v_toGoalState_1283_, 11);
v_extThms_1302_ = lean_ctor_get(v_toGoalState_1283_, 12);
v_ematch_1303_ = lean_ctor_get(v_toGoalState_1283_, 13);
v_inj_1304_ = lean_ctor_get(v_toGoalState_1283_, 14);
v_split_1305_ = lean_ctor_get(v_toGoalState_1283_, 15);
v_clean_1306_ = lean_ctor_get(v_toGoalState_1283_, 16);
v_sstates_1307_ = lean_ctor_get(v_toGoalState_1283_, 17);
v_goalStack_1308_ = lean_ctor_get(v_toGoalState_1283_, 18);
v_introBase_1309_ = lean_ctor_get_uint64(v_toGoalState_1283_, sizeof(void*)*21);
v_numIntros_1310_ = lean_ctor_get(v_toGoalState_1283_, 19);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_toGoalState_1283_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_toGoalState_1283_, 20);
lean_dec(v_unused_1342_);
v___x_1312_ = v_toGoalState_1283_;
v_isShared_1313_ = v_isSharedCheck_1341_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_numIntros_1310_);
lean_inc(v_goalStack_1308_);
lean_inc(v_sstates_1307_);
lean_inc(v_clean_1306_);
lean_inc(v_split_1305_);
lean_inc(v_inj_1304_);
lean_inc(v_ematch_1303_);
lean_inc(v_extThms_1302_);
lean_inc(v_facts_1301_);
lean_inc(v_newRawFacts_1300_);
lean_inc(v_nextIdx_1299_);
lean_inc(v_internalizing_1297_);
lean_inc(v_toProcess_1296_);
lean_inc(v_indicesFound_1295_);
lean_inc(v_appMap_1294_);
lean_inc(v_congrTable_1293_);
lean_inc(v_parents_1292_);
lean_inc(v_exprs_1291_);
lean_inc(v_enodeMap_1290_);
lean_inc(v_nextDeclIdx_1289_);
lean_dec(v_toGoalState_1283_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1341_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_keys_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1339_; 
v_keys_1314_ = lean_ctor_get(v_relevance_1284_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_relevance_1284_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v_relevance_1284_, 1);
lean_dec(v_unused_1340_);
v___x_1316_ = v_relevance_1284_;
v_isShared_1317_ = v_isSharedCheck_1339_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_keys_1314_);
lean_dec(v_relevance_1284_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1339_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_snd_1280_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_keys_1314_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_snd_1280_);
v___x_1319_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 20, v___x_1319_);
v___x_1321_ = v___x_1312_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_nextDeclIdx_1289_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_enodeMap_1290_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_exprs_1291_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_parents_1292_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_congrTable_1293_);
lean_ctor_set(v_reuseFailAlloc_1337_, 5, v_appMap_1294_);
lean_ctor_set(v_reuseFailAlloc_1337_, 6, v_indicesFound_1295_);
lean_ctor_set(v_reuseFailAlloc_1337_, 7, v_toProcess_1296_);
lean_ctor_set(v_reuseFailAlloc_1337_, 8, v_internalizing_1297_);
lean_ctor_set(v_reuseFailAlloc_1337_, 9, v_nextIdx_1299_);
lean_ctor_set(v_reuseFailAlloc_1337_, 10, v_newRawFacts_1300_);
lean_ctor_set(v_reuseFailAlloc_1337_, 11, v_facts_1301_);
lean_ctor_set(v_reuseFailAlloc_1337_, 12, v_extThms_1302_);
lean_ctor_set(v_reuseFailAlloc_1337_, 13, v_ematch_1303_);
lean_ctor_set(v_reuseFailAlloc_1337_, 14, v_inj_1304_);
lean_ctor_set(v_reuseFailAlloc_1337_, 15, v_split_1305_);
lean_ctor_set(v_reuseFailAlloc_1337_, 16, v_clean_1306_);
lean_ctor_set(v_reuseFailAlloc_1337_, 17, v_sstates_1307_);
lean_ctor_set(v_reuseFailAlloc_1337_, 18, v_goalStack_1308_);
lean_ctor_set(v_reuseFailAlloc_1337_, 19, v_numIntros_1310_);
lean_ctor_set(v_reuseFailAlloc_1337_, 20, v___x_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1337_, sizeof(void*)*21 + 8, v_inconsistent_1298_);
lean_ctor_set_uint64(v_reuseFailAlloc_1337_, sizeof(void*)*21, v_introBase_1309_);
v___x_1321_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1321_);
v___x_1323_ = v___x_1287_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_mvarId_1285_);
v___x_1323_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_st_ref_put(v_a_1215_, v___x_1323_);
v___x_1325_ = l_List_reverse___redArg(v_fst_1279_);
v___x_1326_ = lean_box(0);
v___x_1327_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg(v_generation_1214_, v___x_1325_, v___x_1326_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v___x_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1327_, 0);
lean_dec(v_unused_1335_);
v___x_1329_ = v___x_1327_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v___x_1327_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1326_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1326_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
return v___x_1327_;
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
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_snd_1280_);
lean_dec(v_fst_1279_);
lean_dec(v_generation_1214_);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v_skipped_1275_);
lean_dec_ref(v___y_1230_);
lean_dec(v_generation_1214_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
}
}
}
}
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_array_get_size(v___y_1360_);
v___x_1362_ = lean_nat_dec_eq(v___x_1361_, v___x_1358_);
if (v___x_1362_ == 0)
{
lean_object* v_keys_1363_; uint8_t v___x_1364_; 
v_keys_1363_ = lean_ctor_get(v_relevance_1228_, 0);
v___x_1364_ = lean_nat_dec_lt(v___x_1358_, v___x_1361_);
if (v___x_1364_ == 0)
{
lean_inc_ref(v_keys_1363_);
v___y_1230_ = v___y_1360_;
v___y_1231_ = v_keys_1363_;
goto v___jp_1229_;
}
else
{
size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = lean_usize_of_nat(v___x_1361_);
lean_inc_ref(v_keys_1363_);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__6(v___y_1360_, v___x_1365_, v___x_1366_, v_keys_1363_);
v___y_1230_ = v___y_1360_;
v___y_1231_ = v___x_1367_;
goto v___jp_1229_;
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v___y_1360_);
lean_dec_ref(v_relevance_1228_);
lean_dec(v_generation_1214_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg(lean_object* v_generation_1376_, lean_object* v_as_x27_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
if (lean_obj_tag(v_as_x27_1377_) == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_generation_1376_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_b_1378_);
return v___x_1390_;
}
else
{
lean_object* v_toCold_1391_; lean_object* v_options_1392_; lean_object* v_head_1393_; lean_object* v_tail_1394_; lean_object* v_inheritedTraceOptions_1395_; uint8_t v_hasTrace_1396_; lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; 
v_toCold_1391_ = lean_ctor_get(v___y_1387_, 0);
v_options_1392_ = lean_ctor_get(v_toCold_1391_, 2);
v_head_1393_ = lean_ctor_get(v_as_x27_1377_, 0);
v_tail_1394_ = lean_ctor_get(v_as_x27_1377_, 1);
v_inheritedTraceOptions_1395_ = lean_ctor_get(v_toCold_1391_, 11);
v_hasTrace_1396_ = lean_ctor_get_uint8(v_options_1392_, sizeof(void*)*1);
v___x_1397_ = lean_box(0);
if (v_hasTrace_1396_ == 0)
{
v___y_1420_ = v___y_1379_;
v___y_1421_ = v___y_1380_;
v___y_1422_ = v___y_1381_;
v___y_1423_ = v___y_1382_;
v___y_1424_ = v___y_1383_;
v___y_1425_ = v___y_1384_;
v___y_1426_ = v___y_1385_;
v___y_1427_ = v___y_1386_;
v___y_1428_ = v___y_1387_;
v___y_1429_ = v___y_1388_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2));
v___x_1436_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5);
v___x_1437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1395_, v_options_1392_, v___x_1436_);
if (v___x_1437_ == 0)
{
v___y_1420_ = v___y_1379_;
v___y_1421_ = v___y_1380_;
v___y_1422_ = v___y_1381_;
v___y_1423_ = v___y_1382_;
v___y_1424_ = v___y_1383_;
v___y_1425_ = v___y_1384_;
v___y_1426_ = v___y_1385_;
v___y_1427_ = v___y_1386_;
v___y_1428_ = v___y_1387_;
v___y_1429_ = v___y_1388_;
goto v___jp_1419_;
}
else
{
lean_object* v_prop_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_prop_1438_ = lean_ctor_get(v_head_1393_, 1);
v___x_1439_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__7);
lean_inc_ref(v_prop_1438_);
v___x_1440_ = l_Lean_indentExpr(v_prop_1438_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(v___x_1435_, v___x_1441_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
v___y_1420_ = v___y_1379_;
v___y_1421_ = v___y_1380_;
v___y_1422_ = v___y_1381_;
v___y_1423_ = v___y_1382_;
v___y_1424_ = v___y_1383_;
v___y_1425_ = v___y_1384_;
v___y_1426_ = v___y_1385_;
v___y_1427_ = v___y_1386_;
v___y_1428_ = v___y_1387_;
v___y_1429_ = v___y_1388_;
goto v___jp_1419_;
}
else
{
lean_dec(v_generation_1376_);
return v___x_1442_;
}
}
}
v___jp_1398_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_box(6);
v___x_1414_ = lean_box(1);
v___x_1415_ = l_Lean_Meta_Grind_addNewRawFact___redArg(v___y_1409_, v___y_1407_, v___y_1412_, v___x_1413_, v___x_1414_, v___y_1402_, v___y_1406_, v___y_1400_, v___y_1411_, v___y_1401_, v___y_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec_ref_known(v___x_1415_, 1);
v___x_1416_ = l_Lean_Meta_Grind_Relevance_getRelevantKeys(v___y_1403_);
lean_dec_ref(v___y_1403_);
lean_inc(v_generation_1376_);
v___x_1417_ = l_Lean_Meta_Grind_Relevance_registerKeys(v___x_1416_, v_generation_1376_, v___y_1402_, v___y_1404_, v___y_1406_, v___y_1399_, v___y_1410_, v___y_1405_, v___y_1400_, v___y_1411_, v___y_1401_, v___y_1408_);
lean_dec_ref(v___x_1416_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v_as_x27_1377_ = v_tail_1394_;
v_b_1378_ = v___x_1397_;
goto _start;
}
else
{
lean_dec(v_generation_1376_);
return v___x_1417_;
}
}
else
{
lean_dec_ref(v___y_1403_);
lean_dec(v_generation_1376_);
return v___x_1415_;
}
}
v___jp_1419_:
{
lean_object* v_proof_1430_; lean_object* v_prop_1431_; lean_object* v_generation_1432_; lean_object* v_atoms_1433_; uint8_t v___x_1434_; 
v_proof_1430_ = lean_ctor_get(v_head_1393_, 0);
v_prop_1431_ = lean_ctor_get(v_head_1393_, 1);
v_generation_1432_ = lean_ctor_get(v_head_1393_, 2);
v_atoms_1433_ = lean_ctor_get(v_head_1393_, 3);
v___x_1434_ = lean_nat_dec_le(v_generation_1376_, v_generation_1432_);
if (v___x_1434_ == 0)
{
lean_inc(v_generation_1376_);
lean_inc_ref(v_proof_1430_);
lean_inc_ref(v_prop_1431_);
lean_inc_ref(v_atoms_1433_);
v___y_1399_ = v___y_1423_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v_atoms_1433_;
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1422_;
v___y_1407_ = v_prop_1431_;
v___y_1408_ = v___y_1429_;
v___y_1409_ = v_proof_1430_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1427_;
v___y_1412_ = v_generation_1376_;
goto v___jp_1398_;
}
else
{
lean_inc(v_generation_1432_);
lean_inc_ref(v_proof_1430_);
lean_inc_ref(v_prop_1431_);
lean_inc_ref(v_atoms_1433_);
v___y_1399_ = v___y_1423_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v_atoms_1433_;
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1422_;
v___y_1407_ = v_prop_1431_;
v___y_1408_ = v___y_1429_;
v___y_1409_ = v_proof_1430_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1427_;
v___y_1412_ = v_generation_1432_;
goto v___jp_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___boxed(lean_object* v_generation_1443_, lean_object* v_as_x27_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg(v_generation_1443_, v_as_x27_1444_, v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v_as_x27_1444_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Relevance_registerKeys___boxed(lean_object* v_keys_1458_, lean_object* v_generation_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Grind_Relevance_registerKeys(v_keys_1458_, v_generation_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_keys_1458_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0(lean_object* v_00_u03b2_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0___redArg(v_x_1473_, v_x_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4(lean_object* v_cls_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(v_cls_1477_, v_msg_1478_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___boxed(lean_object* v_cls_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4(v_cls_1491_, v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5(lean_object* v_generation_1505_, lean_object* v_as_1506_, lean_object* v_as_x27_1507_, lean_object* v_b_1508_, lean_object* v_a_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg(v_generation_1505_, v_as_x27_1507_, v_b_1508_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___boxed(lean_object* v_generation_1522_, lean_object* v_as_1523_, lean_object* v_as_x27_1524_, lean_object* v_b_1525_, lean_object* v_a_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5(v_generation_1522_, v_as_1523_, v_as_x27_1524_, v_b_1525_, v_a_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec(v_as_x27_1524_);
lean_dec(v_as_1523_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0(lean_object* v_00_u03b2_1539_, lean_object* v_x_1540_, size_t v_x_1541_, size_t v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___redArg(v_x_1540_, v_x_1541_, v_x_1542_, v_x_1543_, v_x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
size_t v_x_33467__boxed_1552_; size_t v_x_33468__boxed_1553_; lean_object* v_res_1554_; 
v_x_33467__boxed_1552_ = lean_unbox_usize(v_x_1548_);
lean_dec(v_x_1548_);
v_x_33468__boxed_1553_ = lean_unbox_usize(v_x_1549_);
lean_dec(v_x_1549_);
v_res_1554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0(v_00_u03b2_1546_, v_x_1547_, v_x_33467__boxed_1552_, v_x_33468__boxed_1553_, v_x_1550_, v_x_1551_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1555_, lean_object* v_n_1556_, lean_object* v_k_1557_, lean_object* v_v_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1___redArg(v_n_1556_, v_k_1557_, v_v_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1560_, size_t v_depth_1561_, lean_object* v_keys_1562_, lean_object* v_vals_1563_, lean_object* v_heq_1564_, lean_object* v_i_1565_, lean_object* v_entries_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___redArg(v_depth_1561_, v_keys_1562_, v_vals_1563_, v_i_1565_, v_entries_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1568_, lean_object* v_depth_1569_, lean_object* v_keys_1570_, lean_object* v_vals_1571_, lean_object* v_heq_1572_, lean_object* v_i_1573_, lean_object* v_entries_1574_){
_start:
{
size_t v_depth_boxed_1575_; lean_object* v_res_1576_; 
v_depth_boxed_1575_ = lean_unbox_usize(v_depth_1569_);
lean_dec(v_depth_1569_);
v_res_1576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__2(v_00_u03b2_1568_, v_depth_boxed_1575_, v_keys_1570_, v_vals_1571_, v_heq_1572_, v_i_1573_, v_entries_1574_);
lean_dec_ref(v_vals_1571_);
lean_dec_ref(v_keys_1570_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10(lean_object* v_00_u03b2_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__0_spec__0_spec__1_spec__10___redArg(v_x_1578_, v_x_1579_, v_x_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(lean_object* v_e_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = l_Lean_Expr_hasMVar(v_e_1583_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_e_1583_);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v_mctx_1589_; lean_object* v___x_1590_; lean_object* v_fst_1591_; lean_object* v_snd_1592_; lean_object* v___x_1593_; lean_object* v_cache_1594_; lean_object* v_zetaDeltaFVarIds_1595_; lean_object* v_postponed_1596_; lean_object* v_diag_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1606_; 
v___x_1588_ = lean_st_ref_get(v___y_1584_);
v_mctx_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc_ref(v_mctx_1589_);
lean_dec(v___x_1588_);
v___x_1590_ = l_Lean_instantiateMVarsCore(v_mctx_1589_, v_e_1583_);
v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_fst_1591_);
v_snd_1592_ = lean_ctor_get(v___x_1590_, 1);
lean_inc(v_snd_1592_);
lean_dec_ref(v___x_1590_);
v___x_1593_ = lean_st_ref_take(v___y_1584_);
v_cache_1594_ = lean_ctor_get(v___x_1593_, 1);
v_zetaDeltaFVarIds_1595_ = lean_ctor_get(v___x_1593_, 2);
v_postponed_1596_ = lean_ctor_get(v___x_1593_, 3);
v_diag_1597_ = lean_ctor_get(v___x_1593_, 4);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1607_);
v___x_1599_ = v___x_1593_;
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_diag_1597_);
lean_inc(v_postponed_1596_);
lean_inc(v_zetaDeltaFVarIds_1595_);
lean_inc(v_cache_1594_);
lean_dec(v___x_1593_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_snd_1592_);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_snd_1592_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_cache_1594_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_zetaDeltaFVarIds_1595_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_postponed_1596_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_diag_1597_);
v___x_1602_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_st_ref_put(v___y_1584_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_fst_1591_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg___boxed(lean_object* v_e_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(v_e_1608_, v___y_1609_);
lean_dec(v___y_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0(lean_object* v_e_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(v_e_1612_, v___y_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___boxed(lean_object* v_e_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0(v_e_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec(v___y_1626_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkIrrelevant_x3f(lean_object* v_prop_1638_, lean_object* v_generation_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
uint8_t v_filterFacts_1651_; 
v_filterFacts_1651_ = lean_ctor_get_uint8(v_a_1642_, sizeof(void*)*13);
if (v_filterFacts_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v_generation_1639_);
lean_dec_ref(v_prop_1638_);
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1702_; 
v___x_1654_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(v_prop_1638_, v_a_1647_);
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1702_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1702_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Meta_Grind_Relevance_checkFact(v_a_1655_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1693_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1693_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1693_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_fst_1664_; uint8_t v___x_1665_; 
v_fst_1664_ = lean_ctor_get(v_a_1660_, 0);
v___x_1665_ = lean_unbox(v_fst_1664_);
if (v___x_1665_ == 0)
{
lean_object* v_snd_1666_; lean_object* v___x_1668_; 
lean_dec(v_generation_1639_);
v_snd_1666_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1666_);
lean_dec(v_a_1660_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 1);
lean_ctor_set(v___x_1657_, 0, v_snd_1666_);
v___x_1668_ = v___x_1657_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_snd_1666_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1668_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_snd_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_del_object(v___x_1662_);
lean_del_object(v___x_1657_);
v_snd_1673_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1673_);
lean_dec(v_a_1660_);
v___x_1674_ = l_Lean_Meta_Grind_Relevance_getRelevantKeys(v_snd_1673_);
lean_dec(v_snd_1673_);
v___x_1675_ = l_Lean_Meta_Grind_Relevance_registerKeys(v___x_1674_, v_generation_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec_ref(v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; 
v_unused_1684_ = lean_ctor_get(v___x_1675_, 0);
lean_dec(v_unused_1684_);
v___x_1677_ = v___x_1675_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v___x_1675_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_box(0);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1675_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1675_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_del_object(v___x_1657_);
lean_dec(v_generation_1639_);
v_a_1694_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1659_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1659_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkIrrelevant_x3f___boxed(lean_object* v_prop_1703_, lean_object* v_generation_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_Grind_checkIrrelevant_x3f(v_prop_1703_, v_generation_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
return v_res_1716_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_skipFact___redArg___closed__1(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Grind_skipFact___redArg___closed__0));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___redArg(lean_object* v_proof_1720_, lean_object* v_prop_1721_, lean_object* v_atoms_1722_, lean_object* v_generation_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___y_1731_; lean_object* v_toCold_1789_; lean_object* v_options_1790_; uint8_t v_hasTrace_1791_; 
v_toCold_1789_ = lean_ctor_get(v_a_1727_, 0);
v_options_1790_ = lean_ctor_get(v_toCold_1789_, 2);
v_hasTrace_1791_ = lean_ctor_get_uint8(v_options_1790_, sizeof(void*)*1);
if (v_hasTrace_1791_ == 0)
{
v___y_1731_ = v_a_1724_;
goto v___jp_1730_;
}
else
{
lean_object* v_inheritedTraceOptions_1792_; lean_object* v_cls_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_inheritedTraceOptions_1792_ = lean_ctor_get(v_toCold_1789_, 11);
v_cls_1793_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2));
v___x_1794_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__5);
v___x_1795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1792_, v_options_1790_, v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1731_ = v_a_1724_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = lean_obj_once(&l_Lean_Meta_Grind_skipFact___redArg___closed__1, &l_Lean_Meta_Grind_skipFact___redArg___closed__1_once, _init_l_Lean_Meta_Grind_skipFact___redArg___closed__1);
lean_inc_ref(v_prop_1721_);
v___x_1797_ = l_Lean_indentExpr(v_prop_1721_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__4___redArg(v_cls_1793_, v___x_1798_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref_known(v___x_1799_, 1);
v___y_1731_ = v_a_1724_;
goto v___jp_1730_;
}
else
{
lean_dec(v_generation_1723_);
lean_dec_ref(v_atoms_1722_);
lean_dec_ref(v_prop_1721_);
lean_dec_ref(v_proof_1720_);
return v___x_1799_;
}
}
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_toGoalState_1734_; lean_object* v_relevance_1735_; lean_object* v_mvarId_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1787_; 
v___x_1732_ = l_Lean_Meta_Grind_Relevance_getSkippedKeys(v_atoms_1722_);
v___x_1733_ = lean_st_ref_take(v___y_1731_);
v_toGoalState_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_toGoalState_1734_);
v_relevance_1735_ = lean_ctor_get(v_toGoalState_1734_, 20);
lean_inc_ref(v_relevance_1735_);
v_mvarId_1736_ = lean_ctor_get(v___x_1733_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1788_);
v___x_1738_ = v___x_1733_;
v_isShared_1739_ = v_isSharedCheck_1787_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_mvarId_1736_);
lean_dec(v___x_1733_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1787_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_nextDeclIdx_1740_; lean_object* v_enodeMap_1741_; lean_object* v_exprs_1742_; lean_object* v_parents_1743_; lean_object* v_congrTable_1744_; lean_object* v_appMap_1745_; lean_object* v_indicesFound_1746_; lean_object* v_toProcess_1747_; lean_object* v_internalizing_1748_; uint8_t v_inconsistent_1749_; lean_object* v_nextIdx_1750_; lean_object* v_newRawFacts_1751_; lean_object* v_facts_1752_; lean_object* v_extThms_1753_; lean_object* v_ematch_1754_; lean_object* v_inj_1755_; lean_object* v_split_1756_; lean_object* v_clean_1757_; lean_object* v_sstates_1758_; lean_object* v_goalStack_1759_; uint64_t v_introBase_1760_; lean_object* v_numIntros_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1785_; 
v_nextDeclIdx_1740_ = lean_ctor_get(v_toGoalState_1734_, 0);
v_enodeMap_1741_ = lean_ctor_get(v_toGoalState_1734_, 1);
v_exprs_1742_ = lean_ctor_get(v_toGoalState_1734_, 2);
v_parents_1743_ = lean_ctor_get(v_toGoalState_1734_, 3);
v_congrTable_1744_ = lean_ctor_get(v_toGoalState_1734_, 4);
v_appMap_1745_ = lean_ctor_get(v_toGoalState_1734_, 5);
v_indicesFound_1746_ = lean_ctor_get(v_toGoalState_1734_, 6);
v_toProcess_1747_ = lean_ctor_get(v_toGoalState_1734_, 7);
v_internalizing_1748_ = lean_ctor_get(v_toGoalState_1734_, 8);
v_inconsistent_1749_ = lean_ctor_get_uint8(v_toGoalState_1734_, sizeof(void*)*21 + 8);
v_nextIdx_1750_ = lean_ctor_get(v_toGoalState_1734_, 9);
v_newRawFacts_1751_ = lean_ctor_get(v_toGoalState_1734_, 10);
v_facts_1752_ = lean_ctor_get(v_toGoalState_1734_, 11);
v_extThms_1753_ = lean_ctor_get(v_toGoalState_1734_, 12);
v_ematch_1754_ = lean_ctor_get(v_toGoalState_1734_, 13);
v_inj_1755_ = lean_ctor_get(v_toGoalState_1734_, 14);
v_split_1756_ = lean_ctor_get(v_toGoalState_1734_, 15);
v_clean_1757_ = lean_ctor_get(v_toGoalState_1734_, 16);
v_sstates_1758_ = lean_ctor_get(v_toGoalState_1734_, 17);
v_goalStack_1759_ = lean_ctor_get(v_toGoalState_1734_, 18);
v_introBase_1760_ = lean_ctor_get_uint64(v_toGoalState_1734_, sizeof(void*)*21);
v_numIntros_1761_ = lean_ctor_get(v_toGoalState_1734_, 19);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_toGoalState_1734_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_toGoalState_1734_, 20);
lean_dec(v_unused_1786_);
v___x_1763_ = v_toGoalState_1734_;
v_isShared_1764_ = v_isSharedCheck_1785_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_numIntros_1761_);
lean_inc(v_goalStack_1759_);
lean_inc(v_sstates_1758_);
lean_inc(v_clean_1757_);
lean_inc(v_split_1756_);
lean_inc(v_inj_1755_);
lean_inc(v_ematch_1754_);
lean_inc(v_extThms_1753_);
lean_inc(v_facts_1752_);
lean_inc(v_newRawFacts_1751_);
lean_inc(v_nextIdx_1750_);
lean_inc(v_internalizing_1748_);
lean_inc(v_toProcess_1747_);
lean_inc(v_indicesFound_1746_);
lean_inc(v_appMap_1745_);
lean_inc(v_congrTable_1744_);
lean_inc(v_parents_1743_);
lean_inc(v_exprs_1742_);
lean_inc(v_enodeMap_1741_);
lean_inc(v_nextDeclIdx_1740_);
lean_dec(v_toGoalState_1734_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1785_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_keys_1765_; lean_object* v_skipped_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1784_; 
v_keys_1765_ = lean_ctor_get(v_relevance_1735_, 0);
v_skipped_1766_ = lean_ctor_get(v_relevance_1735_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_relevance_1735_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1768_ = v_relevance_1735_;
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_skipped_1766_);
lean_inc(v_keys_1765_);
lean_dec(v_relevance_1735_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1771_, 0, v_proof_1720_);
lean_ctor_set(v___x_1771_, 1, v_prop_1721_);
lean_ctor_set(v___x_1771_, 2, v_generation_1723_);
lean_ctor_set(v___x_1771_, 3, v_atoms_1722_);
lean_ctor_set(v___x_1771_, 4, v___x_1732_);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v_skipped_1766_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1772_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_keys_1765_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 20, v___x_1774_);
v___x_1776_ = v___x_1763_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_nextDeclIdx_1740_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_enodeMap_1741_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_exprs_1742_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_parents_1743_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_congrTable_1744_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_appMap_1745_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_indicesFound_1746_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_toProcess_1747_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_internalizing_1748_);
lean_ctor_set(v_reuseFailAlloc_1782_, 9, v_nextIdx_1750_);
lean_ctor_set(v_reuseFailAlloc_1782_, 10, v_newRawFacts_1751_);
lean_ctor_set(v_reuseFailAlloc_1782_, 11, v_facts_1752_);
lean_ctor_set(v_reuseFailAlloc_1782_, 12, v_extThms_1753_);
lean_ctor_set(v_reuseFailAlloc_1782_, 13, v_ematch_1754_);
lean_ctor_set(v_reuseFailAlloc_1782_, 14, v_inj_1755_);
lean_ctor_set(v_reuseFailAlloc_1782_, 15, v_split_1756_);
lean_ctor_set(v_reuseFailAlloc_1782_, 16, v_clean_1757_);
lean_ctor_set(v_reuseFailAlloc_1782_, 17, v_sstates_1758_);
lean_ctor_set(v_reuseFailAlloc_1782_, 18, v_goalStack_1759_);
lean_ctor_set(v_reuseFailAlloc_1782_, 19, v_numIntros_1761_);
lean_ctor_set(v_reuseFailAlloc_1782_, 20, v___x_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*21 + 8, v_inconsistent_1749_);
lean_ctor_set_uint64(v_reuseFailAlloc_1782_, sizeof(void*)*21, v_introBase_1760_);
v___x_1776_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1776_);
v___x_1778_ = v___x_1738_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_mvarId_1736_);
v___x_1778_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_st_ref_put(v___y_1731_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1770_);
return v___x_1780_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___redArg___boxed(lean_object* v_proof_1800_, lean_object* v_prop_1801_, lean_object* v_atoms_1802_, lean_object* v_generation_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Meta_Grind_skipFact___redArg(v_proof_1800_, v_prop_1801_, v_atoms_1802_, v_generation_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact(lean_object* v_proof_1811_, lean_object* v_prop_1812_, lean_object* v_atoms_1813_, lean_object* v_generation_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Grind_skipFact___redArg(v_proof_1811_, v_prop_1812_, v_atoms_1813_, v_generation_1814_, v_a_1815_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_skipFact___boxed(lean_object* v_proof_1827_, lean_object* v_prop_1828_, lean_object* v_atoms_1829_, lean_object* v_generation_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Meta_Grind_skipFact(v_proof_1827_, v_prop_1828_, v_atoms_1829_, v_generation_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec(v_a_1831_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_filterFact(lean_object* v_prop_1843_, lean_object* v_proof_1844_, lean_object* v_generation_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; 
lean_inc(v_generation_1845_);
lean_inc_ref(v_prop_1843_);
v___x_1857_ = l_Lean_Meta_Grind_checkIrrelevant_x3f(v_prop_1843_, v_generation_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1887_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1887_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1887_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
if (lean_obj_tag(v_a_1858_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; 
lean_del_object(v___x_1860_);
v_val_1862_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_a_1858_, 1);
v___x_1863_ = l_Lean_Meta_Grind_skipFact___redArg(v_proof_1844_, v_prop_1843_, v_val_1862_, v_generation_1845_, v_a_1846_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___x_1863_, 0);
lean_dec(v_unused_1873_);
v___x_1865_ = v___x_1863_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v___x_1863_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = 0;
v___x_1868_ = lean_box(v___x_1867_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1868_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1863_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1863_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec(v_a_1858_);
lean_dec(v_generation_1845_);
lean_dec_ref(v_proof_1844_);
lean_dec_ref(v_prop_1843_);
v___x_1882_ = 1;
v___x_1883_ = lean_box(v___x_1882_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1883_);
v___x_1885_ = v___x_1860_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_generation_1845_);
lean_dec_ref(v_proof_1844_);
lean_dec_ref(v_prop_1843_);
v_a_1888_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1857_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1857_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_filterFact___boxed(lean_object* v_prop_1896_, lean_object* v_proof_1897_, lean_object* v_generation_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Meta_Grind_filterFact(v_prop_1896_, v_proof_1897_, v_generation_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerRelevantFact(lean_object* v_prop_1911_, lean_object* v_generation_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
uint8_t v_filterFacts_1924_; 
v_filterFacts_1924_ = lean_ctor_get_uint8(v_a_1915_, sizeof(void*)*13);
if (v_filterFacts_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec(v_generation_1912_);
lean_dec_ref(v_prop_1911_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1929_; 
v___x_1927_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_checkIrrelevant_x3f_spec__0___redArg(v_prop_1911_, v_a_1920_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1915_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___y_1932_; lean_object* v_ematch_1937_; lean_object* v_genLocal_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v_ematch_1937_ = lean_ctor_get(v_a_1930_, 2);
lean_inc(v_ematch_1937_);
v_genLocal_1938_ = lean_ctor_get(v_a_1930_, 4);
lean_inc(v_genLocal_1938_);
lean_dec(v_a_1930_);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_nat_dec_lt(v___x_1939_, v_ematch_1937_);
lean_dec(v_ematch_1937_);
if (v___x_1940_ == 0)
{
lean_dec(v_genLocal_1938_);
v___y_1932_ = v___x_1940_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_lt(v___x_1939_, v_genLocal_1938_);
lean_dec(v_genLocal_1938_);
v___y_1932_ = v___x_1941_;
goto v___jp_1931_;
}
v___jp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_Relevance_getEqFVarSides___closed__0));
v___x_1934_ = l_Lean_Meta_Grind_Relevance_collectAtoms(v_a_1928_, v___y_1932_, v___x_1933_);
v___x_1935_ = l_Lean_Meta_Grind_Relevance_getRelevantKeys(v___x_1934_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = l_Lean_Meta_Grind_Relevance_registerKeys(v___x_1935_, v_generation_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec_ref(v___x_1935_);
return v___x_1936_;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1928_);
lean_dec(v_generation_1912_);
v_a_1942_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1929_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1929_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerRelevantFact___boxed(lean_object* v_prop_1950_, lean_object* v_generation_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Meta_Grind_registerRelevantFact(v_prop_1950_, v_generation_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec(v_a_1952_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_unsigned_to_nat(2530342220u);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_));
v___x_2023_ = l_Lean_Name_num___override(v___x_2022_, v___x_2021_);
return v___x_2023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_));
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_);
v___x_2027_ = l_Lean_Name_str___override(v___x_2026_, v___x_2025_);
return v___x_2027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_));
v___x_2030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_);
v___x_2031_ = l_Lean_Name_str___override(v___x_2030_, v___x_2029_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_unsigned_to_nat(2u);
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_);
v___x_2034_ = l_Lean_Name_num___override(v___x_2033_, v___x_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Relevance_registerKeys_spec__5___redArg___closed__2));
v___x_2037_ = 0;
v___x_2038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_);
v___x_2039_ = l_Lean_registerTraceClass(v___x_2036_, v___x_2037_, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2____boxed(lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_();
return v_res_2041_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Relevance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Relevance_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Relevance_2530342220____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Relevance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Relevance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Relevance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Relevance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Relevance(builtin);
}
#ifdef __cplusplus
}
#endif

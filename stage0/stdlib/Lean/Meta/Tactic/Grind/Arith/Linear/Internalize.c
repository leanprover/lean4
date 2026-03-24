// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.Linear.StructId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Linear.Util import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(249, 76, 129, 208, 175, 107, 80, 215)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " ==> "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(lean_object* v_e_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = l_Lean_Expr_cleanupAnnotations(v_e_51_);
v___x_53_ = l_Lean_Expr_isApp(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec_ref(v___x_52_);
v___x_54_ = lean_box(0);
return v___x_54_;
}
else
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = l_Lean_Expr_appFnCleanup___redArg(v___x_52_);
v___x_56_ = l_Lean_Expr_isApp(v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v___x_55_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v_arg_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_arg_58_ = lean_ctor_get(v___x_55_, 1);
lean_inc_ref(v_arg_58_);
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_55_);
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2));
v___x_61_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5));
v___x_63_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
lean_dec_ref(v_arg_58_);
v___x_64_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v___x_59_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v_arg_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_arg_66_ = lean_ctor_get(v___x_59_, 1);
lean_inc_ref(v_arg_66_);
v___x_67_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11));
v___x_71_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14));
v___x_73_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17));
v___x_75_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
lean_dec_ref(v_arg_66_);
v___x_76_ = l_Lean_Expr_isApp(v___x_67_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v___x_67_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v_arg_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_arg_78_ = lean_ctor_get(v___x_67_, 1);
lean_inc_ref(v_arg_78_);
v___x_79_ = l_Lean_Expr_appFnCleanup___redArg(v___x_67_);
v___x_80_ = l_Lean_Expr_isApp(v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v___x_79_);
lean_dec_ref(v_arg_78_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = l_Lean_Expr_appFnCleanup___redArg(v___x_79_);
v___x_83_ = l_Lean_Expr_isApp(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v___x_82_);
lean_dec_ref(v_arg_78_);
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = l_Lean_Expr_appFnCleanup___redArg(v___x_82_);
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20));
v___x_87_ = l_Lean_Expr_isConstOf(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23));
v___x_89_ = l_Lean_Expr_isConstOf(v___x_85_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26));
v___x_91_ = l_Lean_Expr_isConstOf(v___x_85_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29));
v___x_93_ = l_Lean_Expr_isConstOf(v___x_85_, v___x_92_);
lean_dec_ref(v___x_85_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v_arg_78_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_arg_78_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_85_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v_arg_78_);
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_85_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_arg_78_);
return v___x_97_;
}
}
else
{
lean_object* v___x_98_; 
lean_dec_ref(v___x_85_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_arg_78_);
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec_ref(v___x_67_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v_arg_66_);
return v___x_99_;
}
}
else
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_67_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_arg_66_);
return v___x_100_;
}
}
else
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_67_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_arg_66_);
return v___x_101_;
}
}
else
{
lean_object* v___x_102_; 
lean_dec_ref(v___x_67_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_arg_66_);
return v___x_102_;
}
}
}
else
{
lean_object* v___x_103_; 
lean_dec_ref(v___x_59_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_arg_58_);
return v___x_103_;
}
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_59_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_arg_58_);
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(lean_object* v_parent_x3f_125_){
_start:
{
if (lean_obj_tag(v_parent_x3f_125_) == 1)
{
lean_object* v_val_126_; lean_object* v___x_127_; 
v_val_126_ = lean_ctor_get(v_parent_x3f_125_, 0);
lean_inc(v_val_126_);
lean_dec_ref(v_parent_x3f_125_);
lean_inc(v_val_126_);
v___x_127_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_val_126_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_Expr_cleanupAnnotations(v_val_126_);
v___x_129_ = l_Lean_Expr_isApp(v___x_128_);
if (v___x_129_ == 0)
{
lean_dec_ref(v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_128_);
v___x_131_ = l_Lean_Expr_isApp(v___x_130_);
if (v___x_131_ == 0)
{
lean_dec_ref(v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = l_Lean_Expr_appFnCleanup___redArg(v___x_130_);
v___x_133_ = l_Lean_Expr_isApp(v___x_132_);
if (v___x_133_ == 0)
{
lean_dec_ref(v___x_132_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_132_);
v___x_135_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_135_ == 0)
{
lean_dec_ref(v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2));
v___x_138_ = l_Lean_Expr_isConstOf(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5));
v___x_140_ = l_Lean_Expr_isConstOf(v___x_136_, v___x_139_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Expr_isApp(v___x_136_);
if (v___x_141_ == 0)
{
lean_dec_ref(v___x_136_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_136_);
v___x_143_ = l_Lean_Expr_isApp(v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v___x_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_142_);
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8));
v___x_146_ = l_Lean_Expr_isConstOf(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11));
v___x_148_ = l_Lean_Expr_isConstOf(v___x_144_, v___x_147_);
lean_dec_ref(v___x_144_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
return v___x_135_;
}
}
else
{
lean_dec_ref(v___x_144_);
return v___x_135_;
}
}
}
}
else
{
lean_dec_ref(v___x_136_);
return v___x_135_;
}
}
else
{
lean_dec_ref(v___x_136_);
return v___x_135_;
}
}
}
}
}
}
else
{
uint8_t v___x_149_; 
lean_dec_ref(v___x_127_);
lean_dec(v_val_126_);
v___x_149_ = 1;
return v___x_149_;
}
}
else
{
uint8_t v___x_150_; 
lean_dec(v_parent_x3f_125_);
v___x_150_ = 1;
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___boxed(lean_object* v_parent_x3f_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(lean_object* v_e_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = 1;
v___x_168_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_154_, v___x_167_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_177_);
v___x_170_ = v___x_168_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_dec(v___x_168_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_168_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_168_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar___boxed(lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
return v_res_199_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(lean_object* v_e_200_){
_start:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = l_Lean_Expr_cleanupAnnotations(v_e_200_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_dec_ref(v___x_201_);
return v___x_202_;
}
else
{
lean_object* v_arg_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_arg_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc_ref(v_arg_203_);
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_dec_ref(v___x_204_);
lean_dec_ref(v_arg_203_);
return v___x_205_;
}
else
{
lean_object* v_arg_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_arg_206_ = lean_ctor_get(v___x_204_, 1);
lean_inc_ref(v_arg_206_);
v___x_207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v___x_207_);
lean_dec_ref(v_arg_206_);
lean_dec_ref(v_arg_203_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14));
v___x_211_ = l_Lean_Expr_isConstOf(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
lean_dec_ref(v_arg_206_);
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17));
v___x_213_ = l_Lean_Expr_isConstOf(v___x_209_, v___x_212_);
lean_dec_ref(v___x_209_);
if (v___x_213_ == 0)
{
lean_dec_ref(v_arg_203_);
return v___x_213_;
}
else
{
v_e_200_ = v_arg_203_;
goto _start;
}
}
else
{
uint8_t v___x_215_; 
lean_dec_ref(v___x_209_);
lean_dec_ref(v_arg_203_);
v___x_215_ = l_Lean_Meta_Grind_Arith_isNatNum(v_arg_206_);
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral___boxed(lean_object* v_e_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_e_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_235_; 
lean_inc_ref(v_e_219_);
v___x_235_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_219_, v_a_228_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_Lean_Expr_cleanupAnnotations(v_a_236_);
v___x_238_ = l_Lean_Expr_isApp(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec_ref(v___x_237_);
v___x_239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_239_;
}
else
{
lean_object* v_arg_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_arg_240_ = lean_ctor_get(v___x_237_, 1);
lean_inc_ref(v_arg_240_);
v___x_241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_237_);
v___x_242_ = l_Lean_Expr_isApp(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
v___x_243_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_243_;
}
else
{
lean_object* v_arg_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_arg_244_ = lean_ctor_get(v___x_241_, 1);
lean_inc_ref(v_arg_244_);
v___x_245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_241_);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Expr_isApp(v___x_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec_ref(v___x_245_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_249_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_249_;
}
else
{
lean_object* v_arg_250_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_arg_250_ = lean_ctor_get(v___x_245_, 1);
lean_inc_ref(v_arg_250_);
v___x_287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_245_);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14));
v___x_289_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17));
v___x_291_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_290_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Expr_isApp(v___x_287_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_293_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_287_);
v___x_295_ = l_Lean_Expr_isApp(v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v___x_294_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_296_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_294_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v___x_297_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20));
v___x_302_ = l_Lean_Expr_isConstOf(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23));
v___x_304_ = l_Lean_Expr_isConstOf(v___x_300_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_300_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_300_, v___x_307_);
lean_dec_ref(v___x_300_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_309_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; uint8_t v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_311_, v_arg_250_);
lean_dec_ref(v_arg_250_);
lean_dec(v_a_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v_e_219_);
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
lean_inc_ref(v_a_223_);
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_inc(v_a_220_);
v___x_314_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_dec_ref(v___x_314_);
v_e_219_ = v_arg_240_;
goto _start;
}
else
{
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
return v___x_314_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_316_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_310_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_310_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
else
{
lean_object* v___x_324_; 
lean_dec_ref(v___x_300_);
v___x_324_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; uint8_t v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v___x_324_);
v___x_326_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_325_, v_arg_250_);
lean_dec_ref(v_arg_250_);
lean_dec(v_a_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
lean_dec_ref(v_e_219_);
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
lean_inc_ref(v_a_223_);
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_inc(v_a_220_);
v___x_328_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_dec_ref(v___x_328_);
v_e_219_ = v_arg_240_;
goto _start;
}
else
{
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
return v___x_328_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_330_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_324_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_324_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_object* v___x_338_; 
lean_dec_ref(v___x_300_);
v___x_338_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; uint8_t v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_a_339_, v_arg_250_);
lean_dec_ref(v_arg_250_);
lean_dec(v_a_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
lean_inc_ref(v_arg_244_);
v___x_342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_244_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
lean_inc_ref(v_arg_240_);
v___x_343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_240_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
lean_inc_ref(v_a_223_);
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_inc(v_a_220_);
v___x_344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v___x_344_);
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
lean_inc(v_a_224_);
lean_inc_ref(v_a_223_);
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_inc(v_a_220_);
v___x_345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v___x_346_; 
lean_dec_ref(v___x_345_);
v___x_346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_dec_ref(v___x_346_);
goto v___jp_232_;
}
else
{
return v___x_346_;
}
}
else
{
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
return v___x_345_;
}
}
else
{
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v___x_347_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_347_;
}
}
else
{
lean_object* v___x_348_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_e_219_);
v___x_348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_348_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_349_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_338_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_338_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_300_);
v___x_357_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; uint8_t v___x_359_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_358_, v_arg_250_);
lean_dec(v_a_358_);
if (v___x_359_ == 0)
{
v___y_252_ = v_a_220_;
v___y_253_ = v_a_221_;
v___y_254_ = v_a_222_;
v___y_255_ = v_a_223_;
v___y_256_ = v_a_224_;
v___y_257_ = v_a_225_;
v___y_258_ = v_a_226_;
v___y_259_ = v_a_227_;
v___y_260_ = v_a_228_;
v___y_261_ = v_a_229_;
v___y_262_ = v_a_230_;
goto v___jp_251_;
}
else
{
lean_object* v___x_360_; 
lean_inc(v_a_230_);
lean_inc_ref(v_a_229_);
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc_ref(v_arg_244_);
v___x_360_ = l_Lean_Meta_getIntValue_x3f(v_arg_244_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; uint8_t v___y_363_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref(v___x_360_);
if (lean_obj_tag(v_a_361_) == 0)
{
v___y_363_ = v___x_291_;
goto v___jp_362_;
}
else
{
lean_dec_ref(v_a_361_);
v___y_363_ = v___x_359_;
goto v___jp_362_;
}
v___jp_362_:
{
if (v___y_363_ == 0)
{
v___y_252_ = v_a_220_;
v___y_253_ = v_a_221_;
v___y_254_ = v_a_222_;
v___y_255_ = v_a_223_;
v___y_256_ = v_a_224_;
v___y_257_ = v_a_225_;
v___y_258_ = v_a_226_;
v___y_259_ = v_a_227_;
v___y_260_ = v_a_228_;
v___y_261_ = v_a_229_;
v___y_262_ = v_a_230_;
goto v___jp_251_;
}
else
{
lean_object* v___x_364_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_e_219_);
v___x_364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_364_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_365_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_360_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_360_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
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
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_373_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_357_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_357_);
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
}
}
else
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_e_219_);
v_e_219_ = v_arg_240_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
goto v___jp_232_;
}
v___jp_251_:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref(v___x_263_);
v___x_265_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_264_, v_arg_250_);
lean_dec_ref(v_arg_250_);
lean_dec(v_a_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
v___x_266_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
v___x_267_ = l_Lean_Meta_getNatValue_x3f(v_arg_244_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec_ref(v_arg_244_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_267_);
if (lean_obj_tag(v_a_268_) == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v_arg_240_);
v___x_269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec_ref(v_a_268_);
lean_dec_ref(v_e_219_);
v___x_270_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
return v___x_270_;
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v_a_271_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_267_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_267_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v_a_279_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_263_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_263_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_245_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
goto v___jp_232_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_382_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_235_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_235_);
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
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(lean_object* v_e_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(lean_object* v_cls_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_options_410_; uint8_t v_hasTrace_411_; 
v_options_410_ = lean_ctor_get(v___y_408_, 2);
v_hasTrace_411_ = lean_ctor_get_uint8(v_options_410_, sizeof(void*)*1);
if (v_hasTrace_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v_cls_407_);
v___x_412_ = lean_box(v_hasTrace_411_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
else
{
lean_object* v_inheritedTraceOptions_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_inheritedTraceOptions_414_ = lean_ctor_get(v___y_408_, 13);
v___x_415_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_416_ = l_Lean_Name_append(v___x_415_, v_cls_407_);
v___x_417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_414_, v_options_410_, v___x_416_);
lean_dec(v___x_416_);
v___x_418_ = lean_box(v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(lean_object* v_cls_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_420_, v___y_421_);
lean_dec_ref(v___y_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(lean_object* v_cls_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_424_, v___y_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(lean_object* v_cls_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(v_cls_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
lean_dec(v___y_439_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(lean_object* v_cls_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_options_455_; uint8_t v_hasTrace_456_; 
v_options_455_ = lean_ctor_get(v___y_453_, 2);
v_hasTrace_456_ = lean_ctor_get_uint8(v_options_455_, sizeof(void*)*1);
if (v_hasTrace_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_cls_452_);
v___x_457_ = lean_box(v_hasTrace_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
else
{
lean_object* v_inheritedTraceOptions_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_inheritedTraceOptions_459_ = lean_ctor_get(v___y_453_, 13);
v___x_460_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_461_ = l_Lean_Name_append(v___x_460_, v_cls_452_);
v___x_462_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_459_, v_options_455_, v___x_461_);
lean_dec(v___x_461_);
v___x_463_ = lean_box(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg___boxed(lean_object* v_cls_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v_cls_465_, v___y_466_);
lean_dec_ref(v___y_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2(lean_object* v_cls_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v_cls_469_, v___y_479_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___boxed(lean_object* v_cls_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2(v_cls_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec(v___y_485_);
lean_dec(v___y_484_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(lean_object* v_msgData_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; lean_object* v___x_505_; lean_object* v_mctx_506_; lean_object* v_lctx_507_; lean_object* v_options_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_503_ = lean_st_ref_get(v___y_501_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = lean_st_ref_get(v___y_499_);
v_mctx_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_mctx_506_);
lean_dec(v___x_505_);
v_lctx_507_ = lean_ctor_get(v___y_498_, 2);
v_options_508_ = lean_ctor_get(v___y_500_, 2);
lean_inc_ref(v_options_508_);
lean_inc_ref(v_lctx_507_);
v___x_509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_509_, 0, v_env_504_);
lean_ctor_set(v___x_509_, 1, v_mctx_506_);
lean_ctor_set(v___x_509_, 2, v_lctx_507_);
lean_ctor_set(v___x_509_, 3, v_options_508_);
v___x_510_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_msgData_497_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1___boxed(lean_object* v_msgData_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msgData_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_518_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; double v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_float_of_nat(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(lean_object* v_cls_524_, lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_ref_531_; lean_object* v___x_532_; lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_577_; 
v_ref_531_ = lean_ctor_get(v___y_528_, 5);
v___x_532_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msg_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_577_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_577_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_577_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v_traceState_538_; lean_object* v_env_539_; lean_object* v_nextMacroScope_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_cache_543_; lean_object* v_messages_544_; lean_object* v_infoState_545_; lean_object* v_snapshotTasks_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_576_; 
v___x_537_ = lean_st_ref_take(v___y_529_);
v_traceState_538_ = lean_ctor_get(v___x_537_, 4);
v_env_539_ = lean_ctor_get(v___x_537_, 0);
v_nextMacroScope_540_ = lean_ctor_get(v___x_537_, 1);
v_ngen_541_ = lean_ctor_get(v___x_537_, 2);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_537_, 3);
v_cache_543_ = lean_ctor_get(v___x_537_, 5);
v_messages_544_ = lean_ctor_get(v___x_537_, 6);
v_infoState_545_ = lean_ctor_get(v___x_537_, 7);
v_snapshotTasks_546_ = lean_ctor_get(v___x_537_, 8);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_576_ == 0)
{
v___x_548_ = v___x_537_;
v_isShared_549_ = v_isSharedCheck_576_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snapshotTasks_546_);
lean_inc(v_infoState_545_);
lean_inc(v_messages_544_);
lean_inc(v_cache_543_);
lean_inc(v_traceState_538_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_nextMacroScope_540_);
lean_inc(v_env_539_);
lean_dec(v___x_537_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_576_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint64_t v_tid_550_; lean_object* v_traces_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_575_; 
v_tid_550_ = lean_ctor_get_uint64(v_traceState_538_, sizeof(void*)*1);
v_traces_551_ = lean_ctor_get(v_traceState_538_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_traceState_538_);
if (v_isSharedCheck_575_ == 0)
{
v___x_553_ = v_traceState_538_;
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_traces_551_);
lean_dec(v_traceState_538_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; double v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_555_ = lean_box(0);
v___x_556_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0);
v___x_557_ = 0;
v___x_558_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1));
v___x_559_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_559_, 0, v_cls_524_);
lean_ctor_set(v___x_559_, 1, v___x_555_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
lean_ctor_set_float(v___x_559_, sizeof(void*)*3, v___x_556_);
lean_ctor_set_float(v___x_559_, sizeof(void*)*3 + 8, v___x_556_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*3 + 16, v___x_557_);
v___x_560_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2));
v___x_561_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v_a_533_);
lean_ctor_set(v___x_561_, 2, v___x_560_);
lean_inc(v_ref_531_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_ref_531_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Lean_PersistentArray_push___redArg(v_traces_551_, v___x_562_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_563_);
v___x_565_ = v___x_553_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_563_);
lean_ctor_set_uint64(v_reuseFailAlloc_574_, sizeof(void*)*1, v_tid_550_);
v___x_565_ = v_reuseFailAlloc_574_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 4, v___x_565_);
v___x_567_ = v___x_548_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_env_539_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_nextMacroScope_540_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v_cache_543_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_messages_544_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_infoState_545_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_snapshotTasks_546_);
v___x_567_ = v_reuseFailAlloc_573_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = lean_st_ref_set(v___y_529_, v___x_567_);
v___x_569_ = lean_box(0);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_569_);
v___x_571_ = v___x_535_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(lean_object* v_cls_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_578_, v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(lean_object* v_cls_586_, lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_ref_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_639_; 
v_ref_593_ = lean_ctor_get(v___y_590_, 5);
v___x_594_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msg_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_639_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_639_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_639_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_traceState_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_cache_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_638_; 
v___x_599_ = lean_st_ref_take(v___y_591_);
v_traceState_600_ = lean_ctor_get(v___x_599_, 4);
v_env_601_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_599_, 1);
v_ngen_603_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_599_, 3);
v_cache_605_ = lean_ctor_get(v___x_599_, 5);
v_messages_606_ = lean_ctor_get(v___x_599_, 6);
v_infoState_607_ = lean_ctor_get(v___x_599_, 7);
v_snapshotTasks_608_ = lean_ctor_get(v___x_599_, 8);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_638_ == 0)
{
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_cache_605_);
lean_inc(v_traceState_600_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_637_; 
v_tid_612_ = lean_ctor_get_uint64(v_traceState_600_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_traceState_600_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_traceState_600_);
if (v_isSharedCheck_637_ == 0)
{
v___x_615_ = v_traceState_600_;
v_isShared_616_ = v_isSharedCheck_637_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_traceState_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_637_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; double v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0);
v___x_619_ = 0;
v___x_620_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1));
v___x_621_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_621_, 0, v_cls_586_);
lean_ctor_set(v___x_621_, 1, v___x_617_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set_float(v___x_621_, sizeof(void*)*3, v___x_618_);
lean_ctor_set_float(v___x_621_, sizeof(void*)*3 + 8, v___x_618_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*3 + 16, v___x_619_);
v___x_622_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2));
v___x_623_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v_a_595_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
lean_inc(v_ref_593_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_ref_593_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_PersistentArray_push___redArg(v_traces_613_, v___x_624_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_625_);
v___x_627_ = v___x_615_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_625_);
lean_ctor_set_uint64(v_reuseFailAlloc_636_, sizeof(void*)*1, v_tid_612_);
v___x_627_ = v_reuseFailAlloc_636_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v___x_627_);
v___x_629_ = v___x_610_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_env_601_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_635_, 5, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_635_, 6, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_635_, 7, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_635_, 8, v_snapshotTasks_608_);
v___x_629_ = v_reuseFailAlloc_635_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_630_ = lean_st_ref_set(v___y_591_, v___x_629_);
v___x_631_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_631_);
v___x_633_ = v___x_597_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg___boxed(lean_object* v_cls_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v_cls_640_, v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize(lean_object* v_e_658_, lean_object* v_parent_x3f_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_662_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_790_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_790_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_790_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_790_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v_linarith_705_; 
v_linarith_705_ = lean_ctor_get_uint8(v_a_701_, sizeof(void*)*11 + 22);
lean_dec(v_a_701_);
if (v_linarith_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec(v_parent_x3f_659_);
lean_dec_ref(v_e_658_);
v___x_706_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_659_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_inc_ref(v_e_658_);
v___x_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_e_658_);
if (lean_obj_tag(v___x_711_) == 1)
{
lean_object* v_val_712_; uint8_t v___x_713_; 
v_val_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_659_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_del_object(v___x_703_);
lean_inc(v_a_669_);
lean_inc_ref(v_a_668_);
lean_inc(v_a_667_);
lean_inc_ref(v_a_666_);
lean_inc(v_a_665_);
lean_inc_ref(v_a_664_);
lean_inc(v_a_663_);
lean_inc_ref(v_a_662_);
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_inc(v_val_712_);
v___x_714_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_val_712_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_a_719_; uint8_t v___x_720_; 
lean_dec(v_val_712_);
v_val_716_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_val_716_);
lean_dec_ref(v_a_715_);
v___x_717_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_718_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v___x_717_, v_a_668_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = lean_unbox(v_a_719_);
lean_dec(v_a_719_);
if (v___x_720_ == 0)
{
v___y_672_ = v_val_716_;
v___y_673_ = v_a_660_;
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
v___y_681_ = v_a_668_;
v___y_682_ = v_a_669_;
goto v___jp_671_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc_ref(v_e_658_);
v___x_721_ = l_Lean_MessageData_ofExpr(v_e_658_);
v___x_722_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v___x_717_, v___x_721_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_dec_ref(v___x_722_);
v___y_672_ = v_val_716_;
v___y_673_ = v_a_660_;
v___y_674_ = v_a_661_;
v___y_675_ = v_a_662_;
v___y_676_ = v_a_663_;
v___y_677_ = v_a_664_;
v___y_678_ = v_a_665_;
v___y_679_ = v_a_666_;
v___y_680_ = v_a_667_;
v___y_681_ = v_a_668_;
v___y_682_ = v_a_669_;
goto v___jp_671_;
}
else
{
lean_dec(v_val_716_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
return v___x_722_;
}
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v_a_715_);
lean_inc(v_a_669_);
lean_inc_ref(v_a_668_);
lean_inc(v_a_667_);
lean_inc_ref(v_a_666_);
lean_inc(v_a_665_);
lean_inc_ref(v_a_664_);
lean_inc(v_a_663_);
lean_inc_ref(v_a_662_);
lean_inc(v_a_661_);
lean_inc(v_a_660_);
v___x_723_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_val_712_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_761_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_761_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_761_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_761_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
if (lean_obj_tag(v_a_724_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
lean_del_object(v___x_726_);
v_val_728_ = lean_ctor_get(v_a_724_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v_a_724_);
lean_inc(v_a_669_);
lean_inc_ref(v_a_668_);
lean_inc(v_a_667_);
lean_inc_ref(v_a_666_);
lean_inc(v_a_665_);
lean_inc_ref(v_a_664_);
lean_inc(v_a_663_);
lean_inc_ref(v_a_662_);
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_inc_ref(v_e_658_);
v___x_729_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_658_, v_val_728_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v_fst_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_747_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v_fst_731_ = lean_ctor_get(v_a_730_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_a_730_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_a_730_, 1);
lean_dec(v_unused_748_);
v___x_733_ = v_a_730_;
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_fst_731_);
lean_dec(v_a_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_a_737_; uint8_t v___x_738_; 
v___x_735_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_736_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v___x_735_, v_a_668_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = lean_unbox(v_a_737_);
lean_dec(v_a_737_);
if (v___x_738_ == 0)
{
lean_del_object(v___x_733_);
lean_dec(v_fst_731_);
v___y_688_ = v_a_660_;
v___y_689_ = v_a_661_;
v___y_690_ = v_a_662_;
v___y_691_ = v_a_663_;
v___y_692_ = v_a_664_;
v___y_693_ = v_a_665_;
v___y_694_ = v_a_666_;
v___y_695_ = v_a_667_;
v___y_696_ = v_a_668_;
v___y_697_ = v_a_669_;
goto v___jp_687_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc_ref(v_e_658_);
v___x_739_ = l_Lean_MessageData_ofExpr(v_e_658_);
v___x_740_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5, &l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 7);
lean_ctor_set(v___x_733_, 1, v___x_740_);
lean_ctor_set(v___x_733_, 0, v___x_739_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = l_Lean_MessageData_ofExpr(v_fst_731_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v___x_735_, v___x_744_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec_ref(v___x_745_);
v___y_688_ = v_a_660_;
v___y_689_ = v_a_661_;
v___y_690_ = v_a_662_;
v___y_691_ = v_a_663_;
v___y_692_ = v_a_664_;
v___y_693_ = v_a_665_;
v___y_694_ = v_a_666_;
v___y_695_ = v_a_667_;
v___y_696_ = v_a_668_;
v___y_697_ = v_a_669_;
goto v___jp_687_;
}
else
{
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
v_a_749_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_729_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_729_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
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
else
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v_a_724_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
v___x_757_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_757_);
v___x_759_ = v___x_726_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
v_a_762_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_723_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_723_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_val_712_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
v_a_770_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_714_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_714_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_val_712_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_e_658_);
v___x_778_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_778_);
v___x_780_ = v___x_703_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec(v___x_711_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec(v_parent_x3f_659_);
lean_dec_ref(v_e_658_);
v___x_782_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_782_);
v___x_784_ = v___x_703_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec(v_parent_x3f_659_);
lean_dec_ref(v_e_658_);
v___x_786_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_786_);
v___x_788_ = v___x_703_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec(v_parent_x3f_659_);
lean_dec_ref(v_e_658_);
v_a_791_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_700_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_700_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
v___jp_671_:
{
lean_object* v___x_683_; 
lean_inc(v___y_672_);
lean_inc_ref(v_e_658_);
v___x_683_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_658_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec_ref(v___x_683_);
v___x_684_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_inc(v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v_e_658_);
v___x_685_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_684_, v_e_658_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v___x_686_; 
lean_dec_ref(v___x_685_);
v___x_686_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_658_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_686_;
}
else
{
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_e_658_);
return v___x_685_;
}
}
else
{
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_e_658_);
return v___x_683_;
}
}
v___jp_687_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_699_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_698_, v_e_658_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object* v_e_799_, lean_object* v_parent_x3f_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_Grind_Arith_Linear_internalize(v_e_799_, v_parent_x3f_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(lean_object* v_cls_813_, lean_object* v_msg_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_813_, v_msg_814_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(lean_object* v_cls_828_, lean_object* v_msg_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(v_cls_828_, v_msg_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3(lean_object* v_cls_843_, lean_object* v_msg_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v_cls_843_, v_msg_844_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___boxed(lean_object* v_cls_858_, lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3(v_cls_858_, v_msg_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
return v_res_872_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif

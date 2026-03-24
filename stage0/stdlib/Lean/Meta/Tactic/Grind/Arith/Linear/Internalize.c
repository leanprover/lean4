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
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec(v_a_188_);
lean_dec(v_a_187_);
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
v___x_344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v___x_344_);
v___x_345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v___x_346_; 
lean_dec_ref(v___x_345_);
v___x_346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_346_, 0);
lean_dec(v_unused_355_);
v___x_348_ = v___x_346_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_dec(v___x_346_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
return v___x_346_;
}
}
else
{
lean_dec_ref(v_e_219_);
return v___x_345_;
}
}
else
{
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
return v___x_344_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v___x_356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_244_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_e_219_);
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_357_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v_a_358_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_338_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_338_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
else
{
lean_object* v___x_366_; 
lean_dec_ref(v___x_300_);
v___x_366_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; uint8_t v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_366_);
v___x_368_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_367_, v_arg_250_);
lean_dec(v_a_367_);
if (v___x_368_ == 0)
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
lean_object* v___x_369_; 
lean_inc_ref(v_arg_244_);
v___x_369_ = l_Lean_Meta_getIntValue_x3f(v_arg_244_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; uint8_t v___y_372_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
if (lean_obj_tag(v_a_370_) == 0)
{
v___y_372_ = v___x_291_;
goto v___jp_371_;
}
else
{
lean_dec_ref(v_a_370_);
v___y_372_ = v___x_368_;
goto v___jp_371_;
}
v___jp_371_:
{
if (v___y_372_ == 0)
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
lean_object* v___x_373_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_e_219_);
v___x_373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_240_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_373_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v_a_374_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_369_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_369_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v_arg_250_);
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_e_219_);
v_a_382_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_366_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_366_);
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
lean_dec_ref(v_e_219_);
goto v___jp_232_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_e_219_);
v_a_391_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_235_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_235_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(lean_object* v_cls_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_options_419_; uint8_t v_hasTrace_420_; 
v_options_419_ = lean_ctor_get(v___y_417_, 2);
v_hasTrace_420_ = lean_ctor_get_uint8(v_options_419_, sizeof(void*)*1);
if (v_hasTrace_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v_cls_416_);
v___x_421_ = lean_box(v_hasTrace_420_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
else
{
lean_object* v_inheritedTraceOptions_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_inheritedTraceOptions_423_ = lean_ctor_get(v___y_417_, 13);
v___x_424_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_425_ = l_Lean_Name_append(v___x_424_, v_cls_416_);
v___x_426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_423_, v_options_419_, v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = lean_box(v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(lean_object* v_cls_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_429_, v___y_430_);
lean_dec_ref(v___y_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(lean_object* v_cls_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_433_, v___y_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(lean_object* v_cls_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(v_cls_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec(v___y_449_);
lean_dec(v___y_448_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(lean_object* v_cls_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_options_464_; uint8_t v_hasTrace_465_; 
v_options_464_ = lean_ctor_get(v___y_462_, 2);
v_hasTrace_465_ = lean_ctor_get_uint8(v_options_464_, sizeof(void*)*1);
if (v_hasTrace_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_cls_461_);
v___x_466_ = lean_box(v_hasTrace_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
else
{
lean_object* v_inheritedTraceOptions_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_inheritedTraceOptions_468_ = lean_ctor_get(v___y_462_, 13);
v___x_469_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_470_ = l_Lean_Name_append(v___x_469_, v_cls_461_);
v___x_471_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_468_, v_options_464_, v___x_470_);
lean_dec(v___x_470_);
v___x_472_ = lean_box(v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg___boxed(lean_object* v_cls_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v_cls_474_, v___y_475_);
lean_dec_ref(v___y_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2(lean_object* v_cls_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v_cls_478_, v___y_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___boxed(lean_object* v_cls_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2(v_cls_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
lean_dec(v___y_493_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_env_513_; lean_object* v___x_514_; lean_object* v_mctx_515_; lean_object* v_lctx_516_; lean_object* v_options_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = lean_st_ref_get(v___y_508_);
v_mctx_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_mctx_515_);
lean_dec(v___x_514_);
v_lctx_516_ = lean_ctor_get(v___y_507_, 2);
v_options_517_ = lean_ctor_get(v___y_509_, 2);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_lctx_516_);
v___x_518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_518_, 0, v_env_513_);
lean_ctor_set(v___x_518_, 1, v_mctx_515_);
lean_ctor_set(v___x_518_, 2, v_lctx_516_);
lean_ctor_set(v___x_518_, 3, v_options_517_);
v___x_519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_msgData_506_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1___boxed(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msgData_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; double v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_float_of_nat(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_586_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 5);
v___x_541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_586_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_traceState_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_cache_552_; lean_object* v_messages_553_; lean_object* v_infoState_554_; lean_object* v_snapshotTasks_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_585_; 
v___x_546_ = lean_st_ref_take(v___y_538_);
v_traceState_547_ = lean_ctor_get(v___x_546_, 4);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_546_, 1);
v_ngen_550_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_546_, 3);
v_cache_552_ = lean_ctor_get(v___x_546_, 5);
v_messages_553_ = lean_ctor_get(v___x_546_, 6);
v_infoState_554_ = lean_ctor_get(v___x_546_, 7);
v_snapshotTasks_555_ = lean_ctor_get(v___x_546_, 8);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_585_ == 0)
{
v___x_557_ = v___x_546_;
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snapshotTasks_555_);
lean_inc(v_infoState_554_);
lean_inc(v_messages_553_);
lean_inc(v_cache_552_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint64_t v_tid_559_; lean_object* v_traces_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_584_; 
v_tid_559_ = lean_ctor_get_uint64(v_traceState_547_, sizeof(void*)*1);
v_traces_560_ = lean_ctor_get(v_traceState_547_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_traceState_547_);
if (v_isSharedCheck_584_ == 0)
{
v___x_562_ = v_traceState_547_;
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_traces_560_);
lean_dec(v_traceState_547_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; double v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0);
v___x_566_ = 0;
v___x_567_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1));
v___x_568_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_568_, 0, v_cls_533_);
lean_ctor_set(v___x_568_, 1, v___x_564_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3, v___x_565_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3 + 8, v___x_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3 + 16, v___x_566_);
v___x_569_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2));
v___x_570_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v_a_542_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_inc(v_ref_540_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_ref_540_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_PersistentArray_push___redArg(v_traces_560_, v___x_571_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_572_);
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_572_);
lean_ctor_set_uint64(v_reuseFailAlloc_583_, sizeof(void*)*1, v_tid_559_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v___x_574_);
v___x_576_ = v___x_557_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_env_548_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_cache_552_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_messages_553_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_infoState_554_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_snapshotTasks_555_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_set(v___y_538_, v___x_576_);
v___x_578_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_578_);
v___x_580_ = v___x_544_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(lean_object* v_cls_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(lean_object* v_cls_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_ref_602_; lean_object* v___x_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_648_; 
v_ref_602_ = lean_ctor_get(v___y_599_, 5);
v___x_603_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1_spec__1(v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_648_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_648_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_648_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v_traceState_609_; lean_object* v_env_610_; lean_object* v_nextMacroScope_611_; lean_object* v_ngen_612_; lean_object* v_auxDeclNGen_613_; lean_object* v_cache_614_; lean_object* v_messages_615_; lean_object* v_infoState_616_; lean_object* v_snapshotTasks_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_647_; 
v___x_608_ = lean_st_ref_take(v___y_600_);
v_traceState_609_ = lean_ctor_get(v___x_608_, 4);
v_env_610_ = lean_ctor_get(v___x_608_, 0);
v_nextMacroScope_611_ = lean_ctor_get(v___x_608_, 1);
v_ngen_612_ = lean_ctor_get(v___x_608_, 2);
v_auxDeclNGen_613_ = lean_ctor_get(v___x_608_, 3);
v_cache_614_ = lean_ctor_get(v___x_608_, 5);
v_messages_615_ = lean_ctor_get(v___x_608_, 6);
v_infoState_616_ = lean_ctor_get(v___x_608_, 7);
v_snapshotTasks_617_ = lean_ctor_get(v___x_608_, 8);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_647_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_647_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snapshotTasks_617_);
lean_inc(v_infoState_616_);
lean_inc(v_messages_615_);
lean_inc(v_cache_614_);
lean_inc(v_traceState_609_);
lean_inc(v_auxDeclNGen_613_);
lean_inc(v_ngen_612_);
lean_inc(v_nextMacroScope_611_);
lean_inc(v_env_610_);
lean_dec(v___x_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_647_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint64_t v_tid_621_; lean_object* v_traces_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_646_; 
v_tid_621_ = lean_ctor_get_uint64(v_traceState_609_, sizeof(void*)*1);
v_traces_622_ = lean_ctor_get(v_traceState_609_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_traceState_609_);
if (v_isSharedCheck_646_ == 0)
{
v___x_624_ = v_traceState_609_;
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_traces_622_);
lean_dec(v_traceState_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; double v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__0);
v___x_628_ = 0;
v___x_629_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__1));
v___x_630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_630_, 0, v_cls_595_);
lean_ctor_set(v___x_630_, 1, v___x_626_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set_float(v___x_630_, sizeof(void*)*3, v___x_627_);
lean_ctor_set_float(v___x_630_, sizeof(void*)*3 + 8, v___x_627_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*3 + 16, v___x_628_);
v___x_631_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___closed__2));
v___x_632_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v_a_604_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_inc(v_ref_602_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_ref_602_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_PersistentArray_push___redArg(v_traces_622_, v___x_633_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_634_);
v___x_636_ = v___x_624_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_634_);
lean_ctor_set_uint64(v_reuseFailAlloc_645_, sizeof(void*)*1, v_tid_621_);
v___x_636_ = v_reuseFailAlloc_645_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v___x_636_);
v___x_638_ = v___x_619_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_env_610_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_nextMacroScope_611_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_ngen_612_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_auxDeclNGen_613_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v_cache_614_);
lean_ctor_set(v_reuseFailAlloc_644_, 6, v_messages_615_);
lean_ctor_set(v_reuseFailAlloc_644_, 7, v_infoState_616_);
lean_ctor_set(v_reuseFailAlloc_644_, 8, v_snapshotTasks_617_);
v___x_638_ = v_reuseFailAlloc_644_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_639_ = lean_st_ref_set(v___y_600_, v___x_638_);
v___x_640_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_640_);
v___x_642_ = v___x_606_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg___boxed(lean_object* v_cls_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v_cls_649_, v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize(lean_object* v_e_667_, lean_object* v_parent_x3f_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_671_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_799_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_799_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_799_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_799_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v_linarith_714_; 
v_linarith_714_ = lean_ctor_get_uint8(v_a_710_, sizeof(void*)*11 + 22);
lean_dec(v_a_710_);
if (v_linarith_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_parent_x3f_668_);
lean_dec_ref(v_e_667_);
v___x_715_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_668_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_inc_ref(v_e_667_);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_e_667_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; uint8_t v___x_722_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_668_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_del_object(v___x_712_);
lean_inc(v_val_721_);
v___x_723_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_val_721_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
if (lean_obj_tag(v_a_724_) == 1)
{
lean_object* v_val_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_a_728_; uint8_t v___x_729_; 
lean_dec(v_val_721_);
v_val_725_ = lean_ctor_get(v_a_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v_a_724_);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_727_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v___x_726_, v_a_677_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = lean_unbox(v_a_728_);
lean_dec(v_a_728_);
if (v___x_729_ == 0)
{
v___y_681_ = v_val_725_;
v___y_682_ = v_a_669_;
v___y_683_ = v_a_670_;
v___y_684_ = v_a_671_;
v___y_685_ = v_a_672_;
v___y_686_ = v_a_673_;
v___y_687_ = v_a_674_;
v___y_688_ = v_a_675_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
goto v___jp_680_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_inc_ref(v_e_667_);
v___x_730_ = l_Lean_MessageData_ofExpr(v_e_667_);
v___x_731_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v___x_726_, v___x_730_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref(v___x_731_);
v___y_681_ = v_val_725_;
v___y_682_ = v_a_669_;
v___y_683_ = v_a_670_;
v___y_684_ = v_a_671_;
v___y_685_ = v_a_672_;
v___y_686_ = v_a_673_;
v___y_687_ = v_a_674_;
v___y_688_ = v_a_675_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
goto v___jp_680_;
}
else
{
lean_dec(v_val_725_);
lean_dec_ref(v_e_667_);
return v___x_731_;
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v_a_724_);
v___x_732_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_val_721_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_770_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_770_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_770_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_770_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; 
lean_del_object(v___x_735_);
v_val_737_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_val_737_);
lean_dec_ref(v_a_733_);
lean_inc_ref(v_e_667_);
v___x_738_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_667_, v_val_737_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_val_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v_fst_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_756_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v_fst_740_ = lean_ctor_get(v_a_739_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_a_739_, 1);
lean_dec(v_unused_757_);
v___x_742_ = v_a_739_;
v_isShared_743_ = v_isSharedCheck_756_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_fst_740_);
lean_dec(v_a_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_756_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; uint8_t v___x_747_; 
v___x_744_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_745_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__2___redArg(v___x_744_, v_a_677_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_745_);
v___x_747_ = lean_unbox(v_a_746_);
lean_dec(v_a_746_);
if (v___x_747_ == 0)
{
lean_del_object(v___x_742_);
lean_dec(v_fst_740_);
v___y_697_ = v_a_669_;
v___y_698_ = v_a_670_;
v___y_699_ = v_a_671_;
v___y_700_ = v_a_672_;
v___y_701_ = v_a_673_;
v___y_702_ = v_a_674_;
v___y_703_ = v_a_675_;
v___y_704_ = v_a_676_;
v___y_705_ = v_a_677_;
v___y_706_ = v_a_678_;
goto v___jp_696_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
lean_inc_ref(v_e_667_);
v___x_748_ = l_Lean_MessageData_ofExpr(v_e_667_);
v___x_749_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5, &l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 7);
lean_ctor_set(v___x_742_, 1, v___x_749_);
lean_ctor_set(v___x_742_, 0, v___x_748_);
v___x_751_ = v___x_742_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = l_Lean_MessageData_ofExpr(v_fst_740_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v___x_744_, v___x_753_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_dec_ref(v___x_754_);
v___y_697_ = v_a_669_;
v___y_698_ = v_a_670_;
v___y_699_ = v_a_671_;
v___y_700_ = v_a_672_;
v___y_701_ = v_a_673_;
v___y_702_ = v_a_674_;
v___y_703_ = v_a_675_;
v___y_704_ = v_a_676_;
v___y_705_ = v_a_677_;
v___y_706_ = v_a_678_;
goto v___jp_696_;
}
else
{
lean_dec_ref(v_e_667_);
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_e_667_);
v_a_758_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_738_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_738_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v_a_733_);
lean_dec_ref(v_e_667_);
v___x_766_ = lean_box(0);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_766_);
v___x_768_ = v___x_735_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
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
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_e_667_);
v_a_771_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_732_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_732_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_val_721_);
lean_dec_ref(v_e_667_);
v_a_779_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_723_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_723_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_val_721_);
lean_dec_ref(v_e_667_);
v___x_787_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_787_);
v___x_789_ = v___x_712_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_793_; 
lean_dec(v___x_720_);
lean_dec(v_parent_x3f_668_);
lean_dec_ref(v_e_667_);
v___x_791_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_791_);
v___x_793_ = v___x_712_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_dec(v_parent_x3f_668_);
lean_dec_ref(v_e_667_);
v___x_795_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_795_);
v___x_797_ = v___x_712_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_parent_x3f_668_);
lean_dec_ref(v_e_667_);
v_a_800_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_709_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_709_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
v___jp_680_:
{
lean_object* v___x_692_; 
lean_inc_ref(v_e_667_);
v___x_692_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_667_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v___x_692_);
v___x_693_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_inc_ref(v_e_667_);
v___x_694_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_693_, v_e_667_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v___x_694_);
v___x_695_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_667_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_681_);
return v___x_695_;
}
else
{
lean_dec(v___y_681_);
lean_dec_ref(v_e_667_);
return v___x_694_;
}
}
else
{
lean_dec(v___y_681_);
lean_dec_ref(v_e_667_);
return v___x_692_;
}
}
v___jp_696_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_708_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_707_, v_e_667_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object* v_e_808_, lean_object* v_parent_x3f_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Meta_Grind_Arith_Linear_internalize(v_e_808_, v_parent_x3f_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(lean_object* v_cls_822_, lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_822_, v_msg_823_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(lean_object* v_cls_837_, lean_object* v_msg_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(v_cls_837_, v_msg_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3(lean_object* v_cls_852_, lean_object* v_msg_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___redArg(v_cls_852_, v_msg_853_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3___boxed(lean_object* v_cls_867_, lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__3(v_cls_867_, v_msg_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
return v_res_881_;
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

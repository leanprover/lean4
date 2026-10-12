// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule import Init.Grind.Module.Envelope import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.Linear.StructId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Linear.Util import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__12_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__13_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__16_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " ==> "};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(lean_object* v_parent_x3f_136_){
_start:
{
if (lean_obj_tag(v_parent_x3f_136_) == 1)
{
lean_object* v_val_137_; lean_object* v___x_138_; 
v_val_137_ = lean_ctor_get(v_parent_x3f_136_, 0);
lean_inc_n(v_val_137_, 2);
lean_dec_ref_known(v_parent_x3f_136_, 1);
v___x_138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_val_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
uint8_t v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = 0;
v___x_140_ = l_Lean_Expr_cleanupAnnotations(v_val_137_);
v___x_141_ = l_Lean_Expr_isApp(v___x_140_);
if (v___x_141_ == 0)
{
lean_dec_ref(v___x_140_);
return v___x_139_;
}
else
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_140_);
v___x_143_ = l_Lean_Expr_isApp(v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v___x_142_);
return v___x_139_;
}
else
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_142_);
v___x_145_ = l_Lean_Expr_isApp(v___x_144_);
if (v___x_145_ == 0)
{
lean_dec_ref(v___x_144_);
return v___x_139_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_144_);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5));
v___x_148_ = l_Lean_Expr_isConstOf(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = l_Lean_Expr_isApp(v___x_146_);
if (v___x_149_ == 0)
{
lean_dec_ref(v___x_146_);
return v___x_139_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_146_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8));
v___x_152_ = l_Lean_Expr_isConstOf(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11));
v___x_154_ = l_Lean_Expr_isConstOf(v___x_150_, v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Expr_isApp(v___x_150_);
if (v___x_155_ == 0)
{
lean_dec_ref(v___x_150_);
return v___x_139_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_150_);
v___x_157_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_157_ == 0)
{
lean_dec_ref(v___x_156_);
return v___x_139_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__14));
v___x_160_ = l_Lean_Expr_isConstOf(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__17));
v___x_162_ = l_Lean_Expr_isConstOf(v___x_158_, v___x_161_);
lean_dec_ref(v___x_158_);
if (v___x_162_ == 0)
{
return v___x_139_;
}
else
{
return v___x_145_;
}
}
else
{
lean_dec_ref(v___x_158_);
return v___x_145_;
}
}
}
}
else
{
lean_dec_ref(v___x_150_);
return v___x_145_;
}
}
else
{
lean_dec_ref(v___x_150_);
return v___x_145_;
}
}
}
else
{
lean_dec_ref(v___x_146_);
return v___x_145_;
}
}
}
}
}
else
{
uint8_t v___x_163_; 
lean_dec_ref_known(v___x_138_, 1);
lean_dec(v_val_137_);
v___x_163_ = 1;
return v___x_163_;
}
}
else
{
uint8_t v___x_164_; 
lean_dec(v_parent_x3f_136_);
v___x_164_ = 1;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___boxed(lean_object* v_parent_x3f_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = 1;
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v_e_168_, v___x_181_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_191_);
v___x_185_ = v___x_183_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_dec(v___x_183_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_182_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_182_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_183_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_183_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar___boxed(lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec(v_a_202_);
lean_dec(v_a_201_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(lean_object* v_e_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = l_Lean_Expr_cleanupAnnotations(v_e_214_);
v___x_216_ = l_Lean_Expr_isApp(v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_arg_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_arg_217_ = lean_ctor_get(v___x_215_, 1);
lean_inc_ref(v_arg_217_);
v___x_218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_215_);
v___x_219_ = l_Lean_Expr_isApp(v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_218_);
lean_dec_ref(v_arg_217_);
return v___x_219_;
}
else
{
lean_object* v_arg_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_arg_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_arg_220_);
v___x_221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_218_);
v___x_222_ = l_Lean_Expr_isApp(v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v___x_221_);
lean_dec_ref(v_arg_220_);
lean_dec_ref(v_arg_217_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_221_);
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14));
v___x_225_ = l_Lean_Expr_isConstOf(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; uint8_t v___x_227_; 
lean_dec_ref(v_arg_220_);
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17));
v___x_227_ = l_Lean_Expr_isConstOf(v___x_223_, v___x_226_);
lean_dec_ref(v___x_223_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_arg_217_);
return v___x_227_;
}
else
{
v_e_214_ = v_arg_217_;
goto _start;
}
}
else
{
uint8_t v___x_229_; 
lean_dec_ref(v___x_223_);
lean_dec_ref(v_arg_217_);
v___x_229_ = l_Lean_Meta_Grind_Arith_isNatNum(v_arg_220_);
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral___boxed(lean_object* v_e_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_e_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars(lean_object* v_e_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_249_; 
lean_inc_ref(v_e_233_);
v___x_249_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_233_, v_a_242_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = l_Lean_Expr_cleanupAnnotations(v_a_250_);
v___x_252_ = l_Lean_Expr_isApp(v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v___x_251_);
v___x_253_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_253_;
}
else
{
lean_object* v_arg_254_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; uint8_t v___y_267_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_arg_254_ = lean_ctor_get(v___x_251_, 1);
lean_inc_ref(v_arg_254_);
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_251_);
v___x_271_ = l_Lean_Expr_isApp(v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v___x_270_);
lean_dec_ref(v_arg_254_);
v___x_272_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_272_;
}
else
{
lean_object* v_arg_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_arg_273_ = lean_ctor_get(v___x_270_, 1);
lean_inc_ref(v_arg_273_);
v___x_274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_270_);
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5));
v___x_276_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_Expr_isApp(v___x_274_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_278_;
}
else
{
lean_object* v_arg_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_arg_279_ = lean_ctor_get(v___x_274_, 1);
lean_inc_ref(v_arg_279_);
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_274_);
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14));
v___x_282_ = l_Lean_Expr_isConstOf(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17));
v___x_284_ = l_Lean_Expr_isConstOf(v___x_280_, v___x_283_);
if (v___x_284_ == 0)
{
uint8_t v___x_319_; 
v___x_319_ = l_Lean_Expr_isApp(v___x_280_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v___x_280_);
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_280_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_321_);
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_326_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26));
v___x_333_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29));
v___x_335_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_334_);
lean_dec_ref(v___x_327_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_336_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; uint8_t v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_338_, v_arg_279_);
lean_dec_ref(v_arg_279_);
lean_dec(v_a_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_e_233_);
v___x_341_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_273_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_dec_ref_known(v___x_341_, 1);
v_e_233_ = v_arg_254_;
goto _start;
}
else
{
lean_dec_ref(v_arg_254_);
return v___x_341_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_343_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_337_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_337_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
else
{
lean_object* v___x_351_; 
lean_dec_ref(v___x_327_);
v___x_351_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; uint8_t v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_352_, v_arg_279_);
lean_dec_ref(v_arg_279_);
lean_dec(v_a_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; 
lean_dec_ref(v_e_233_);
v___x_355_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_273_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_dec_ref_known(v___x_355_, 1);
v_e_233_ = v_arg_254_;
goto _start;
}
else
{
lean_dec_ref(v_arg_254_);
return v___x_355_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_357_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_351_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_351_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v___x_327_);
v___x_365_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; uint8_t v___x_367_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v___x_367_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_a_366_, v_arg_279_);
lean_dec_ref(v_arg_279_);
lean_dec(v_a_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
lean_inc_ref(v_arg_273_);
v___x_369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_273_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
lean_inc_ref(v_arg_254_);
v___x_370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_254_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_273_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
lean_dec_ref_known(v___x_371_, 1);
v___x_372_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_254_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec_ref_known(v___x_372_, 1);
v___x_373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v___x_373_, 0);
lean_dec(v_unused_382_);
v___x_375_ = v___x_373_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_dec(v___x_373_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_box(0);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
return v___x_373_;
}
}
else
{
lean_dec_ref(v_e_233_);
return v___x_372_;
}
}
else
{
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
return v___x_371_;
}
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v___x_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_273_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_383_;
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_e_233_);
v___x_384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_254_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_384_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_385_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_365_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_365_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_327_);
v___x_393_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; uint8_t v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_394_, v_arg_279_);
lean_dec(v_a_394_);
if (v___x_395_ == 0)
{
v___y_286_ = v_a_234_;
v___y_287_ = v_a_235_;
v___y_288_ = v_a_236_;
v___y_289_ = v_a_237_;
v___y_290_ = v_a_238_;
v___y_291_ = v_a_239_;
v___y_292_ = v_a_240_;
v___y_293_ = v_a_241_;
v___y_294_ = v_a_242_;
v___y_295_ = v_a_243_;
v___y_296_ = v_a_244_;
goto v___jp_285_;
}
else
{
lean_object* v___x_396_; 
lean_inc_ref(v_arg_273_);
v___x_396_ = l_Lean_Meta_getIntValue_x3f(v_arg_273_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; uint8_t v___y_399_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
if (lean_obj_tag(v_a_397_) == 0)
{
v___y_399_ = v___x_284_;
goto v___jp_398_;
}
else
{
lean_dec_ref_known(v_a_397_, 1);
v___y_399_ = v___x_395_;
goto v___jp_398_;
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
v___y_286_ = v_a_234_;
v___y_287_ = v_a_235_;
v___y_288_ = v_a_236_;
v___y_289_ = v_a_237_;
v___y_290_ = v_a_238_;
v___y_291_ = v_a_239_;
v___y_292_ = v_a_240_;
v___y_293_ = v_a_241_;
v___y_294_ = v_a_242_;
v___y_295_ = v_a_243_;
v___y_296_ = v_a_244_;
goto v___jp_285_;
}
else
{
lean_object* v___x_400_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_e_233_);
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_254_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
return v___x_400_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_401_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_396_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_396_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_409_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_393_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_393_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
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
}
}
else
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_e_233_);
v_e_233_ = v_arg_254_;
goto _start;
}
v___jp_285_:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; uint8_t v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_298_, v_arg_279_);
lean_dec_ref(v_arg_279_);
lean_dec(v_a_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
v___x_300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_getNatValue_x3f(v_arg_273_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec_ref(v_arg_273_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
if (lean_obj_tag(v_a_302_) == 0)
{
v___y_256_ = v___y_290_;
v___y_257_ = v___y_296_;
v___y_258_ = v___y_288_;
v___y_259_ = v___y_294_;
v___y_260_ = v___y_292_;
v___y_261_ = v___y_287_;
v___y_262_ = v___y_286_;
v___y_263_ = v___y_295_;
v___y_264_ = v___y_293_;
v___y_265_ = v___y_289_;
v___y_266_ = v___y_291_;
v___y_267_ = v___x_284_;
goto v___jp_255_;
}
else
{
lean_dec_ref_known(v_a_302_, 1);
v___y_256_ = v___y_290_;
v___y_257_ = v___y_296_;
v___y_258_ = v___y_288_;
v___y_259_ = v___y_294_;
v___y_260_ = v___y_292_;
v___y_261_ = v___y_287_;
v___y_262_ = v___y_286_;
v___y_263_ = v___y_295_;
v___y_264_ = v___y_293_;
v___y_265_ = v___y_289_;
v___y_266_ = v___y_291_;
v___y_267_ = v___x_299_;
goto v___jp_255_;
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_303_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
v_a_311_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_297_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_297_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v_arg_279_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
goto v___jp_246_;
}
}
}
else
{
lean_dec_ref(v___x_274_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_254_);
lean_dec_ref(v_e_233_);
goto v___jp_246_;
}
}
v___jp_255_:
{
if (v___y_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v_arg_254_);
v___x_268_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_233_, v___y_262_, v___y_261_, v___y_258_, v___y_265_, v___y_256_, v___y_266_, v___y_260_, v___y_264_, v___y_259_, v___y_263_, v___y_257_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_dec_ref(v_e_233_);
v___x_269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_254_, v___y_262_, v___y_261_, v___y_258_, v___y_265_, v___y_256_, v___y_266_, v___y_260_, v___y_264_, v___y_259_, v___y_263_, v___y_257_);
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_e_233_);
v_a_418_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_249_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_249_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
v___jp_246_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_env_447_; uint8_t v___x_448_; lean_object* v_env_449_; lean_object* v___x_450_; lean_object* v_toCold_451_; lean_object* v_mctx_452_; lean_object* v_lctx_453_; lean_object* v_options_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_446_ = lean_st_ref_get(v___y_444_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_env_447_);
lean_dec(v___x_446_);
v___x_448_ = 0;
v_env_449_ = l_Lean_Environment_setRecordingDeps(v_env_447_, v___x_448_);
v___x_450_ = lean_st_ref_get(v___y_442_);
v_toCold_451_ = lean_ctor_get(v___y_443_, 0);
v_mctx_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_mctx_452_);
lean_dec(v___x_450_);
v_lctx_453_ = lean_ctor_get(v___y_441_, 2);
v_options_454_ = lean_ctor_get(v_toCold_451_, 2);
lean_inc_ref(v_options_454_);
lean_inc_ref(v_lctx_453_);
v___x_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_455_, 0, v_env_449_);
lean_ctor_set(v___x_455_, 1, v_mctx_452_);
lean_ctor_set(v___x_455_, 2, v_lctx_453_);
lean_ctor_set(v___x_455_, 3, v_options_454_);
v___x_456_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_msgData_440_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0___boxed(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msgData_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_464_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_465_; double v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_float_of_nat(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(lean_object* v_cls_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_ref_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_524_; 
v_ref_477_ = lean_ctor_get(v___y_474_, 2);
v___x_478_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_524_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_524_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_524_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v_traceState_484_; lean_object* v_env_485_; lean_object* v_nextMacroScope_486_; lean_object* v_ngen_487_; lean_object* v_auxDeclNGen_488_; lean_object* v_cache_489_; lean_object* v_recordedDeps_490_; lean_object* v_messages_491_; lean_object* v_infoState_492_; lean_object* v_snapshotTasks_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_523_; 
v___x_483_ = lean_st_ref_take(v___y_475_);
v_traceState_484_ = lean_ctor_get(v___x_483_, 4);
v_env_485_ = lean_ctor_get(v___x_483_, 0);
v_nextMacroScope_486_ = lean_ctor_get(v___x_483_, 1);
v_ngen_487_ = lean_ctor_get(v___x_483_, 2);
v_auxDeclNGen_488_ = lean_ctor_get(v___x_483_, 3);
v_cache_489_ = lean_ctor_get(v___x_483_, 5);
v_recordedDeps_490_ = lean_ctor_get(v___x_483_, 6);
v_messages_491_ = lean_ctor_get(v___x_483_, 7);
v_infoState_492_ = lean_ctor_get(v___x_483_, 8);
v_snapshotTasks_493_ = lean_ctor_get(v___x_483_, 9);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_523_ == 0)
{
v___x_495_ = v___x_483_;
v_isShared_496_ = v_isSharedCheck_523_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_snapshotTasks_493_);
lean_inc(v_infoState_492_);
lean_inc(v_messages_491_);
lean_inc(v_recordedDeps_490_);
lean_inc(v_cache_489_);
lean_inc(v_traceState_484_);
lean_inc(v_auxDeclNGen_488_);
lean_inc(v_ngen_487_);
lean_inc(v_nextMacroScope_486_);
lean_inc(v_env_485_);
lean_dec(v___x_483_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_523_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint64_t v_tid_497_; lean_object* v_traces_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_522_; 
v_tid_497_ = lean_ctor_get_uint64(v_traceState_484_, sizeof(void*)*1);
v_traces_498_ = lean_ctor_get(v_traceState_484_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_traceState_484_);
if (v_isSharedCheck_522_ == 0)
{
v___x_500_ = v_traceState_484_;
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_traces_498_);
lean_dec(v_traceState_484_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_502_ = lean_box(0);
v___x_503_ = lean_box(0);
v___x_504_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0);
v___x_505_ = 0;
v___x_506_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_507_, 0, v_cls_470_);
lean_ctor_set(v___x_507_, 1, v___x_503_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_ctor_set_float(v___x_507_, sizeof(void*)*3, v___x_504_);
lean_ctor_set_float(v___x_507_, sizeof(void*)*3 + 8, v___x_504_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 16, v___x_505_);
v___x_508_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2));
v___x_509_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v_a_479_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
lean_inc(v_ref_477_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_ref_477_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = l_Lean_PersistentArray_push___redArg(v_traces_498_, v___x_510_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_511_);
v___x_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_511_);
lean_ctor_set_uint64(v_reuseFailAlloc_521_, sizeof(void*)*1, v_tid_497_);
v___x_513_ = v_reuseFailAlloc_521_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 4, v___x_513_);
v___x_515_ = v___x_495_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_env_485_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_nextMacroScope_486_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_ngen_487_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_auxDeclNGen_488_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v_cache_489_);
lean_ctor_set(v_reuseFailAlloc_520_, 6, v_recordedDeps_490_);
lean_ctor_set(v_reuseFailAlloc_520_, 7, v_messages_491_);
lean_ctor_set(v_reuseFailAlloc_520_, 8, v_infoState_492_);
lean_ctor_set(v_reuseFailAlloc_520_, 9, v_snapshotTasks_493_);
v___x_515_ = v_reuseFailAlloc_520_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_st_ref_put(v___y_475_, v___x_515_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_502_);
v___x_518_ = v___x_481_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_502_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(lean_object* v_cls_525_, lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_525_, v_msg_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_587_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 2);
v___x_541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_587_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_587_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_587_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_traceState_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_cache_552_; lean_object* v_recordedDeps_553_; lean_object* v_messages_554_; lean_object* v_infoState_555_; lean_object* v_snapshotTasks_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_586_; 
v___x_546_ = lean_st_ref_take(v___y_538_);
v_traceState_547_ = lean_ctor_get(v___x_546_, 4);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_546_, 1);
v_ngen_550_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_546_, 3);
v_cache_552_ = lean_ctor_get(v___x_546_, 5);
v_recordedDeps_553_ = lean_ctor_get(v___x_546_, 6);
v_messages_554_ = lean_ctor_get(v___x_546_, 7);
v_infoState_555_ = lean_ctor_get(v___x_546_, 8);
v_snapshotTasks_556_ = lean_ctor_get(v___x_546_, 9);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_586_ == 0)
{
v___x_558_ = v___x_546_;
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snapshotTasks_556_);
lean_inc(v_infoState_555_);
lean_inc(v_messages_554_);
lean_inc(v_recordedDeps_553_);
lean_inc(v_cache_552_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint64_t v_tid_560_; lean_object* v_traces_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_tid_560_ = lean_ctor_get_uint64(v_traceState_547_, sizeof(void*)*1);
v_traces_561_ = lean_ctor_get(v_traceState_547_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_traceState_547_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_traceState_547_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_traces_561_);
lean_dec(v_traceState_547_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; double v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_box(0);
v___x_567_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0);
v___x_568_ = 0;
v___x_569_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1));
v___x_570_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_570_, 0, v_cls_533_);
lean_ctor_set(v___x_570_, 1, v___x_566_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_ctor_set_float(v___x_570_, sizeof(void*)*3, v___x_567_);
lean_ctor_set_float(v___x_570_, sizeof(void*)*3 + 8, v___x_567_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*3 + 16, v___x_568_);
v___x_571_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2));
v___x_572_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v_a_542_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
lean_inc(v_ref_540_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_ref_540_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_PersistentArray_push___redArg(v_traces_561_, v___x_573_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_574_);
v___x_576_ = v___x_563_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_574_);
lean_ctor_set_uint64(v_reuseFailAlloc_584_, sizeof(void*)*1, v_tid_560_);
v___x_576_ = v_reuseFailAlloc_584_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_576_);
v___x_578_ = v___x_558_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_env_548_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v_cache_552_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_recordedDeps_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_messages_554_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_infoState_555_);
lean_ctor_set(v_reuseFailAlloc_583_, 9, v_snapshotTasks_556_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_st_ref_put(v___y_538_, v___x_578_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_565_);
v___x_581_ = v___x_544_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_565_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(lean_object* v_cls_588_, lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_588_, v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_607_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5));
v___x_608_ = l_Lean_Name_append(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize(lean_object* v_e_612_, lean_object* v_parent_x3f_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_616_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_751_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_751_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_751_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_751_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v_linarith_659_; 
v_linarith_659_ = lean_ctor_get_uint8(v_a_655_, sizeof(void*)*14 + 22);
lean_dec(v_a_655_);
if (v_linarith_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec(v_parent_x3f_613_);
lean_dec_ref(v_e_612_);
v___x_660_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_613_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_inc_ref(v_e_612_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_e_612_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; uint8_t v___x_667_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_613_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_del_object(v___x_657_);
lean_inc(v_val_666_);
v___x_668_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_val_666_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
if (lean_obj_tag(v_a_669_) == 1)
{
lean_object* v_toCold_670_; lean_object* v_options_671_; uint8_t v_hasTrace_672_; 
lean_dec(v_val_666_);
v_toCold_670_ = lean_ctor_get(v_a_622_, 0);
v_options_671_ = lean_ctor_get(v_toCold_670_, 2);
v_hasTrace_672_ = lean_ctor_get_uint8(v_options_671_, sizeof(void*)*1);
if (v_hasTrace_672_ == 0)
{
lean_object* v_val_673_; 
v_val_673_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_a_669_, 1);
v___y_639_ = v_val_673_;
v___y_640_ = v_a_614_;
v___y_641_ = v_a_615_;
v___y_642_ = v_a_616_;
v___y_643_ = v_a_617_;
v___y_644_ = v_a_618_;
v___y_645_ = v_a_619_;
v___y_646_ = v_a_620_;
v___y_647_ = v_a_621_;
v___y_648_ = v_a_622_;
v___y_649_ = v_a_623_;
goto v___jp_638_;
}
else
{
lean_object* v_val_674_; lean_object* v_inheritedTraceOptions_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_val_674_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_a_669_, 1);
v_inheritedTraceOptions_675_ = lean_ctor_get(v_toCold_670_, 11);
v___x_676_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_677_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6, &l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6);
v___x_678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_675_, v_options_671_, v___x_677_);
if (v___x_678_ == 0)
{
v___y_639_ = v_val_674_;
v___y_640_ = v_a_614_;
v___y_641_ = v_a_615_;
v___y_642_ = v_a_616_;
v___y_643_ = v_a_617_;
v___y_644_ = v_a_618_;
v___y_645_ = v_a_619_;
v___y_646_ = v_a_620_;
v___y_647_ = v_a_621_;
v___y_648_ = v_a_622_;
v___y_649_ = v_a_623_;
goto v___jp_638_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_inc_ref(v_e_612_);
v___x_679_ = l_Lean_MessageData_ofExpr(v_e_612_);
v___x_680_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v___x_676_, v___x_679_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref_known(v___x_680_, 1);
v___y_639_ = v_val_674_;
v___y_640_ = v_a_614_;
v___y_641_ = v_a_615_;
v___y_642_ = v_a_616_;
v___y_643_ = v_a_617_;
v___y_644_ = v_a_618_;
v___y_645_ = v_a_619_;
v___y_646_ = v_a_620_;
v___y_647_ = v_a_621_;
v___y_648_ = v_a_622_;
v___y_649_ = v_a_623_;
goto v___jp_638_;
}
else
{
lean_dec(v_val_674_);
lean_dec_ref(v_e_612_);
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_681_; 
lean_dec(v_a_669_);
v___x_681_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_val_666_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_722_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_722_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_722_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_722_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
if (lean_obj_tag(v_a_682_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
lean_del_object(v___x_684_);
v_val_686_ = lean_ctor_get(v_a_682_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v_a_682_, 1);
lean_inc_ref(v_e_612_);
v___x_687_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_612_, v_val_686_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_val_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_toCold_689_; lean_object* v_options_690_; uint8_t v_hasTrace_691_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v_toCold_689_ = lean_ctor_get(v_a_622_, 0);
v_options_690_ = lean_ctor_get(v_toCold_689_, 2);
v_hasTrace_691_ = lean_ctor_get_uint8(v_options_690_, sizeof(void*)*1);
if (v_hasTrace_691_ == 0)
{
lean_dec(v_a_688_);
v___y_626_ = v_a_614_;
v___y_627_ = v_a_615_;
v___y_628_ = v_a_616_;
v___y_629_ = v_a_617_;
v___y_630_ = v_a_618_;
v___y_631_ = v_a_619_;
v___y_632_ = v_a_620_;
v___y_633_ = v_a_621_;
v___y_634_ = v_a_622_;
v___y_635_ = v_a_623_;
goto v___jp_625_;
}
else
{
lean_object* v_fst_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_708_; 
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_a_688_, 1);
lean_dec(v_unused_709_);
v___x_694_ = v_a_688_;
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_fst_692_);
lean_dec(v_a_688_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_inheritedTraceOptions_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_inheritedTraceOptions_696_ = lean_ctor_get(v_toCold_689_, 11);
v___x_697_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3));
v___x_698_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6, &l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6);
v___x_699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_696_, v_options_690_, v___x_698_);
if (v___x_699_ == 0)
{
lean_del_object(v___x_694_);
lean_dec(v_fst_692_);
v___y_626_ = v_a_614_;
v___y_627_ = v_a_615_;
v___y_628_ = v_a_616_;
v___y_629_ = v_a_617_;
v___y_630_ = v_a_618_;
v___y_631_ = v_a_619_;
v___y_632_ = v_a_620_;
v___y_633_ = v_a_621_;
v___y_634_ = v_a_622_;
v___y_635_ = v_a_623_;
goto v___jp_625_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc_ref(v_e_612_);
v___x_700_ = l_Lean_MessageData_ofExpr(v_e_612_);
v___x_701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8, &l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 7);
lean_ctor_set(v___x_694_, 1, v___x_701_);
lean_ctor_set(v___x_694_, 0, v___x_700_);
v___x_703_ = v___x_694_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = l_Lean_MessageData_ofExpr(v_fst_692_);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v___x_697_, v___x_705_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v___y_626_ = v_a_614_;
v___y_627_ = v_a_615_;
v___y_628_ = v_a_616_;
v___y_629_ = v_a_617_;
v___y_630_ = v_a_618_;
v___y_631_ = v_a_619_;
v___y_632_ = v_a_620_;
v___y_633_ = v_a_621_;
v___y_634_ = v_a_622_;
v___y_635_ = v_a_623_;
goto v___jp_625_;
}
else
{
lean_dec_ref(v_e_612_);
return v___x_706_;
}
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_e_612_);
v_a_710_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_687_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_687_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec(v_a_682_);
lean_dec_ref(v_e_612_);
v___x_718_ = lean_box(0);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_718_);
v___x_720_ = v___x_684_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_e_612_);
v_a_723_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_681_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_681_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_val_666_);
lean_dec_ref(v_e_612_);
v_a_731_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_668_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_668_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec(v_val_666_);
lean_dec_ref(v_e_612_);
v___x_739_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_739_);
v___x_741_ = v___x_657_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v___x_665_);
lean_dec(v_parent_x3f_613_);
lean_dec_ref(v_e_612_);
v___x_743_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_743_);
v___x_745_ = v___x_657_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v_parent_x3f_613_);
lean_dec_ref(v_e_612_);
v___x_747_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_747_);
v___x_749_ = v___x_657_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
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
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_parent_x3f_613_);
lean_dec_ref(v_e_612_);
v_a_752_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_654_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_654_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
v___jp_625_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_637_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_636_, v_e_612_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_650_; 
lean_inc_ref(v_e_612_);
v___x_650_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_612_, v___y_639_, v___y_640_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref_known(v___x_650_, 1);
v___x_651_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_inc_ref(v_e_612_);
v___x_652_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_651_, v_e_612_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; 
lean_dec_ref_known(v___x_652_, 1);
v___x_653_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_e_612_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_639_);
return v___x_653_;
}
else
{
lean_dec(v___y_639_);
lean_dec_ref(v_e_612_);
return v___x_652_;
}
}
else
{
lean_dec(v___y_639_);
lean_dec_ref(v_e_612_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object* v_e_760_, lean_object* v_parent_x3f_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_Grind_Arith_Linear_internalize(v_e_760_, v_parent_x3f_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(lean_object* v_cls_774_, lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v_cls_774_, v_msg_775_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(lean_object* v_cls_789_, lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(v_cls_789_, v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec(v___y_792_);
lean_dec(v___y_791_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(lean_object* v_cls_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v_cls_804_, v_msg_805_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(lean_object* v_cls_819_, lean_object* v_msg_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(v_cls_819_, v_msg_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v___y_821_);
return v_res_833_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
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
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
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
res = initialize_Init_Grind_Module_Envelope(builtin);
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

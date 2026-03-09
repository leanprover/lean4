// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Init.Grind.ToIntLemmas import Init.GrindInstances.ToInt import Lean.Meta.Tactic.Grind.SynthInstance import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.EvalNum
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "`ToInt` initialization failure, failed to synthesize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nfor type"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "`grind cutsat`, unexpected missing declaration "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_mkIntNeg(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 155, 160, 222, 187, 19, 79, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unsupported `ToInt` interval"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "IntInterval"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "co"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(83, 30, 229, 226, 125, 93, 199, 242)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 155, 142, 59, 173, 125, 172, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8_value;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(83, 30, 229, 226, 125, 93, 199, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 249, 151, 171, 150, 156, 160, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wrap"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(83, 30, 229, 226, 125, 93, 199, 242)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 79, 126, 171, 32, 109, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "registered toInt: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_upper'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(145, 225, 247, 106, 7, 183, 63, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "le_upper"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(91, 220, 75, 219, 186, 199, 45, 76)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(3, 71, 255, 70, 33, 116, 234, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "of_diseq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(185, 194, 44, 124, 53, 182, 161, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ge_lower"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(182, 183, 189, 123, 238, 60, 158, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ge_lower0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(71, 195, 26, 188, 88, 183, 46, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ge_lower'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(43, 151, 107, 19, 98, 132, 29, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "of_eq_wrap_co_0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(71, 165, 93, 156, 204, 99, 224, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "failed to synthesize "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 141, 190, 142, 68, 208, 129, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 96, 26, 113, 82, 2, 198, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_not_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(96, 27, 82, 166, 220, 7, 151, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 142, 125, 208, 167, 144, 43, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(120, 69, 34, 120, 233, 88, 123, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_not_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(97, 248, 151, 91, 249, 217, 36, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 192, 51, 134, 187, 116, 61, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pow_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(43, 15, 154, 172, 198, 254, 54, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6_value;
extern lean_object* l_Lean_Nat_mkType;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ww"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 123, 139, 231, 153, 237, 25, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 223, 148, 101, 92, 235, 2, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 86, 49, 184, 105, 160, 15, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__6_value;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 31, 98, 206, 21, 52, 61, 168)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 134, 178, 212, 229, 217, 60, 200)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 50, 219, 228, 204, 142, 182, 246)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sub_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 111, 111, 13, 133, 127, 37, 68)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "neg_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 221, 229, 164, 59, 40, 119, 252)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Div"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 247, 56, 19, 64, 245, 190, 87)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "div_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 73, 86, 163, 16, 132, 161, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mod"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 157, 192, 123, 66, 123, 34, 2)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mod_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 33, 156, 176, 163, 128, 4, 35)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "zero_eq"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 161, 243, 153, 51, 146, 20)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__6_value;
lean_object* l_Lean_mkBVar(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(51, 109, 133, 142, 196, 189, 255, 155)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNat_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(137, 11, 182, 3, 193, 241, 176, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10_value;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`grind cutsat`, `ToInt` interval not supported yet"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 84, 52, 176, 228, 163, 228, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat_spec__0(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__10_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__11_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__16_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__17_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__19_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__20_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__23_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkIntAdd, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__25_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkIntMul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__26_value;
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ofNat_FinZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__27_value),LEAN_SCALAR_PTR_LITERAL(227, 212, 33, 171, 115, 113, 69, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Meta.Grind.Arith.Cutsat.assertToIntBounds"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5;
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__2));
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__1));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__0));
x_4 = l_Lean_Name_mkStr4(x_3, x_2, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_27; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__3);
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg(x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
x_11 = x_9;
x_12 = x_27;
goto block_26;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_13; 
x_13 = lean_unbox(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_14);
x_15 = x_11;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_11);
x_18 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__5);
x_19 = l_Lean_indentExpr(x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1(x_8, x_24, x_3, x_4, x_5, x_6);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___closed__1);
x_8 = 0;
x_9 = l_Lean_MessageData_ofConstName(x_1, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg(x_10, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = 1;
lean_inc(x_1);
x_10 = l_Lean_Environment_contains(x_8, x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_throwMissingDecl(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_Grind_Arith_evalInt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_28; 
x_13 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_14 = x_12;
x_15 = x_28;
goto block_27;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_mkIntLit(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_23);
x_24 = x_14;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_12, 0);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
x_30 = x_12;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0);
x_5 = lean_int_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
x_5 = x_3;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_int_neg(x_4);
lean_dec(x_4);
x_8 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0);
x_9 = lean_int_add(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_mkIntLit(x_9);
lean_dec(x_9);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_10);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_mkIntNeg(x_16);
x_18 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__1);
x_19 = l_Lean_mkIntAdd(x_17, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_17; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_17 = l_Lean_Meta_whnfD(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_18);
x_19 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_18, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_52; uint8_t x_53; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_52 = l_Lean_Expr_cleanupAnnotations(x_20);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec_ref(x_52);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
goto block_51;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec_ref(x_55);
lean_dec_ref(x_54);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_57);
x_58 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_59 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__8));
x_60 = l_Lean_Expr_isConstOf(x_58, x_59);
lean_dec_ref(x_58);
if (x_60 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_54);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
goto block_51;
}
else
{
lean_object* x_61; 
lean_dec(x_18);
lean_dec_ref(x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound(x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_normalizeBound(x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_73; 
x_64 = lean_ctor_get(x_63, 0);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
x_65 = x_63;
x_66 = x_73;
goto block_72;
}
else
{
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_68);
x_69 = x_65;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_62);
x_74 = lean_ctor_get(x_63, 0);
x_81 = !lean_is_exclusive(x_63);
if (x_81 == 0)
{
x_75 = x_63;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_63);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec_ref(x_54);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_82 = lean_ctor_get(x_61, 0);
x_89 = !lean_is_exclusive(x_61);
if (x_89 == 0)
{
x_83 = x_61;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_61);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
}
block_51:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1));
x_32 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(x_31, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_18);
lean_dec_ref(x_1);
goto block_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__3);
x_36 = l_Lean_indentExpr(x_18);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter___closed__7);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_1);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(x_31, x_41, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
goto block_16;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_43 = lean_ctor_get(x_42, 0);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
x_44 = x_42;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_19, 0);
x_97 = !lean_is_exclusive(x_19);
if (x_97 == 0)
{
x_91 = x_19;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_19);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_17, 0);
x_105 = !lean_is_exclusive(x_17);
if (x_105 == 0)
{
x_99 = x_17;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_17);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 12, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_14, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_49; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_ctor_get(x_14, 3);
x_19 = lean_ctor_get(x_14, 4);
x_20 = lean_ctor_get(x_14, 5);
x_21 = lean_ctor_get(x_14, 6);
x_22 = lean_ctor_get(x_14, 7);
x_23 = lean_ctor_get(x_14, 8);
x_24 = lean_ctor_get(x_14, 9);
x_25 = lean_ctor_get(x_14, 10);
x_26 = lean_ctor_get(x_14, 11);
x_27 = lean_ctor_get(x_14, 12);
x_28 = lean_ctor_get(x_14, 13);
x_29 = lean_ctor_get(x_14, 14);
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*23);
x_31 = lean_ctor_get(x_14, 15);
x_32 = lean_ctor_get(x_14, 16);
x_33 = lean_ctor_get(x_14, 17);
x_34 = lean_ctor_get(x_14, 18);
x_35 = lean_ctor_get(x_14, 19);
x_36 = lean_ctor_get(x_14, 20);
x_37 = lean_ctor_get(x_14, 21);
x_38 = lean_ctor_get_uint8(x_14, sizeof(void*)*23 + 1);
x_39 = lean_ctor_get(x_14, 22);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_40 = x_14;
x_41 = x_49;
goto block_48;
}
else
{
lean_inc(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_3);
lean_ctor_set(x_43, 3, x_4);
lean_ctor_set(x_43, 4, x_5);
lean_ctor_set(x_43, 5, x_6);
lean_ctor_set(x_43, 6, x_7);
lean_ctor_set(x_43, 7, x_8);
lean_ctor_set(x_43, 8, x_9);
lean_ctor_set(x_43, 9, x_10);
lean_ctor_set(x_43, 10, x_11);
lean_ctor_set(x_43, 11, x_12);
lean_ctor_set(x_43, 12, x_13);
lean_ctor_set(x_43, 13, x_42);
lean_ctor_set(x_43, 14, x_42);
lean_ctor_set(x_43, 15, x_42);
lean_ctor_set(x_43, 16, x_42);
lean_ctor_set(x_43, 17, x_42);
lean_ctor_set(x_43, 18, x_42);
lean_ctor_set(x_43, 19, x_42);
lean_ctor_set(x_43, 20, x_42);
lean_ctor_set(x_43, 21, x_42);
lean_ctor_set(x_43, 22, x_42);
lean_ctor_set(x_43, 23, x_42);
lean_ctor_set(x_43, 24, x_42);
lean_ctor_set(x_43, 25, x_42);
x_44 = l_Lean_PersistentArray_push___redArg(x_35, x_43);
if (x_41 == 0)
{
lean_ctor_set(x_40, 19, x_44);
x_45 = x_40;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_16);
lean_ctor_set(x_47, 2, x_17);
lean_ctor_set(x_47, 3, x_18);
lean_ctor_set(x_47, 4, x_19);
lean_ctor_set(x_47, 5, x_20);
lean_ctor_set(x_47, 6, x_21);
lean_ctor_set(x_47, 7, x_22);
lean_ctor_set(x_47, 8, x_23);
lean_ctor_set(x_47, 9, x_24);
lean_ctor_set(x_47, 10, x_25);
lean_ctor_set(x_47, 11, x_26);
lean_ctor_set(x_47, 12, x_27);
lean_ctor_set(x_47, 13, x_28);
lean_ctor_set(x_47, 14, x_29);
lean_ctor_set(x_47, 15, x_31);
lean_ctor_set(x_47, 16, x_32);
lean_ctor_set(x_47, 17, x_33);
lean_ctor_set(x_47, 18, x_34);
lean_ctor_set(x_47, 19, x_44);
lean_ctor_set(x_47, 20, x_36);
lean_ctor_set(x_47, 21, x_37);
lean_ctor_set(x_47, 22, x_39);
lean_ctor_set_uint8(x_47, sizeof(void*)*23, x_30);
lean_ctor_set_uint8(x_47, sizeof(void*)*23 + 1, x_38);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__26));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__28));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_getLevel(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_18 = l_Lean_Meta_decLevel_x3f(x_17, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_323; 
x_19 = lean_ctor_get(x_18, 0);
x_323 = !lean_is_exclusive(x_18);
if (x_323 == 0)
{
x_20 = x_18;
x_21 = x_323;
goto block_322;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_323;
goto block_322;
}
block_322:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_del_object(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = lean_box(0);
x_24 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__2);
x_25 = 0;
x_26 = lean_box(0);
lean_inc_ref(x_8);
x_27 = l_Lean_Meta_mkFreshExprMVar(x_24, x_25, x_26, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4));
lean_inc(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_inc_ref(x_30);
x_31 = l_Lean_mkConst(x_29, x_30);
lean_inc(x_28);
lean_inc_ref(x_1);
x_32 = l_Lean_mkAppB(x_31, x_1, x_28);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_32);
x_33 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_32, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_285; 
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_34, 0);
x_285 = !lean_is_exclusive(x_34);
if (x_285 == 0)
{
x_36 = x_34;
x_37 = x_285;
goto block_284;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__0___redArg(x_28, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_39);
lean_inc_ref(x_1);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f(x_1, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_275; 
x_41 = lean_ctor_get(x_40, 0);
x_275 = !lean_is_exclusive(x_40);
if (x_275 == 0)
{
x_42 = x_40;
x_43 = x_275;
goto block_274;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_275;
goto block_274;
}
block_274:
{
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_269; 
lean_del_object(x_42);
x_44 = lean_ctor_get(x_41, 0);
x_269 = !lean_is_exclusive(x_41);
if (x_269 == 0)
{
x_45 = x_41;
x_46 = x_269;
goto block_268;
}
else
{
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_47 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5));
lean_inc_ref(x_30);
x_48 = l_Lean_mkConst(x_47, x_30);
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_49 = l_Lean_mkApp3(x_48, x_1, x_39, x_35);
x_50 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__8);
lean_inc(x_39);
x_51 = l_Lean_Expr_app___override(x_50, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_247 = lean_ctor_get(x_44, 0);
x_248 = lean_ctor_get(x_44, 1);
x_249 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero(x_247);
if (x_249 == 0)
{
lean_object* x_250; 
lean_del_object(x_36);
x_250 = lean_box(0);
x_176 = x_250;
x_177 = x_2;
x_178 = x_8;
x_179 = x_9;
x_180 = x_10;
x_181 = x_11;
goto block_246;
}
else
{
lean_object* x_251; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_39);
x_251 = l_Lean_Meta_mkEqRefl(x_39, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = lean_ctor_get(x_248, 0);
x_254 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__27);
lean_inc_ref(x_253);
lean_inc(x_39);
x_255 = l_Lean_mkApp3(x_254, x_39, x_253, x_252);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_255);
x_256 = x_36;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_255);
x_256 = x_258;
goto block_257;
}
block_257:
{
x_176 = x_256;
x_177 = x_2;
x_178 = x_8;
x_179 = x_9;
x_180 = x_10;
x_181 = x_11;
goto block_246;
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_266; 
lean_dec_ref(x_44);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_259 = lean_ctor_get(x_251, 0);
x_266 = !lean_is_exclusive(x_251);
if (x_266 == 0)
{
x_260 = x_251;
x_261 = x_266;
goto block_265;
}
else
{
lean_inc(x_259);
lean_dec(x_251);
x_260 = lean_box(0);
x_261 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_262; 
if (x_261 == 0)
{
x_262 = x_260;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_259);
x_262 = x_264;
goto block_263;
}
block_263:
{
return x_262;
}
}
}
}
}
else
{
lean_object* x_267; 
lean_del_object(x_36);
x_267 = lean_box(0);
x_176 = x_267;
x_177 = x_2;
x_178 = x_8;
x_179 = x_9;
x_180 = x_10;
x_181 = x_11;
goto block_246;
}
block_93:
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_57, x_58);
lean_dec_ref(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 19);
lean_inc_ref(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_62);
x_63 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__0), 14, 13);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_1);
lean_closure_set(x_63, 2, x_22);
lean_closure_set(x_63, 3, x_35);
lean_closure_set(x_63, 4, x_39);
lean_closure_set(x_63, 5, x_44);
lean_closure_set(x_63, 6, x_49);
lean_closure_set(x_63, 7, x_51);
lean_closure_set(x_63, 8, x_52);
lean_closure_set(x_63, 9, x_54);
lean_closure_set(x_63, 10, x_53);
lean_closure_set(x_63, 11, x_56);
lean_closure_set(x_63, 12, x_55);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_65 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_64, x_63, x_57);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; uint8_t x_75; 
x_75 = !lean_is_exclusive(x_65);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_65, 0);
lean_dec(x_76);
x_66 = x_65;
x_67 = x_75;
goto block_74;
}
else
{
lean_dec(x_65);
x_66 = lean_box(0);
x_67 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_68; 
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_62);
x_68 = x_45;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_62);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_68);
x_69 = x_66;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_62);
lean_del_object(x_45);
x_77 = lean_ctor_get(x_65, 0);
x_84 = !lean_is_exclusive(x_65);
if (x_84 == 0)
{
x_78 = x_65;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_22);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_59, 0);
x_92 = !lean_is_exclusive(x_59);
if (x_92 == 0)
{
x_86 = x_59;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_59);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
block_120:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1));
x_105 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(x_104, x_95);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_96);
x_52 = x_94;
x_53 = x_97;
x_54 = x_98;
x_55 = x_103;
x_56 = x_99;
x_57 = x_102;
x_58 = x_95;
goto block_93;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__10);
lean_inc_ref(x_1);
x_109 = l_Lean_MessageData_ofExpr(x_1);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(x_104, x_110, x_100, x_96, x_95, x_101);
lean_dec(x_101);
lean_dec(x_96);
lean_dec_ref(x_100);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_52 = x_94;
x_53 = x_97;
x_54 = x_98;
x_55 = x_103;
x_56 = x_99;
x_57 = x_102;
x_58 = x_95;
goto block_93;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_103);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_22);
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_111, 0);
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
x_113 = x_111;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
}
block_175:
{
lean_object* x_130; 
lean_inc(x_44);
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(x_44);
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_173; 
x_131 = lean_ctor_get(x_130, 0);
x_173 = !lean_is_exclusive(x_130);
if (x_173 == 0)
{
x_132 = x_130;
x_133 = x_173;
goto block_172;
}
else
{
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_box(0);
x_133 = x_173;
goto block_172;
}
block_172:
{
uint8_t x_134; 
x_134 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_135);
lean_dec(x_131);
x_136 = l_Lean_Int_mkType;
lean_inc(x_127);
lean_inc_ref(x_122);
lean_inc(x_123);
lean_inc_ref(x_126);
lean_inc_ref(x_135);
x_137 = l_Lean_Meta_mkSome(x_136, x_135, x_126, x_123, x_122, x_127);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
lean_inc(x_127);
lean_inc_ref(x_122);
lean_inc(x_123);
lean_inc_ref(x_126);
x_139 = l_Lean_Meta_mkEqRefl(x_138, x_126, x_123, x_122, x_127);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__12));
x_142 = l_Lean_mkConst(x_141, x_30);
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_143 = l_Lean_mkApp5(x_142, x_1, x_39, x_35, x_135, x_140);
if (x_133 == 0)
{
lean_ctor_set(x_132, 0, x_143);
x_144 = x_132;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
x_94 = x_121;
x_95 = x_122;
x_96 = x_123;
x_97 = x_124;
x_98 = x_125;
x_99 = x_129;
x_100 = x_126;
x_101 = x_127;
x_102 = x_128;
x_103 = x_144;
goto block_120;
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_154; 
lean_dec_ref(x_135);
lean_del_object(x_132);
lean_dec(x_129);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_139, 0);
x_154 = !lean_is_exclusive(x_139);
if (x_154 == 0)
{
x_148 = x_139;
x_149 = x_154;
goto block_153;
}
else
{
lean_inc(x_147);
lean_dec(x_139);
x_148 = lean_box(0);
x_149 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_150; 
if (x_149 == 0)
{
x_150 = x_148;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_147);
x_150 = x_152;
goto block_151;
}
block_151:
{
return x_150;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec_ref(x_135);
lean_del_object(x_132);
lean_dec(x_129);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_137, 0);
x_162 = !lean_is_exclusive(x_137);
if (x_162 == 0)
{
x_156 = x_137;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_137);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg(x_131);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__14));
x_166 = l_Lean_mkConst(x_165, x_30);
x_167 = l_Lean_eagerReflBoolTrue;
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_168 = l_Lean_mkApp5(x_166, x_1, x_39, x_35, x_164, x_167);
if (x_133 == 0)
{
lean_ctor_set(x_132, 0, x_168);
x_169 = x_132;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_168);
x_169 = x_171;
goto block_170;
}
block_170:
{
x_94 = x_121;
x_95 = x_122;
x_96 = x_123;
x_97 = x_124;
x_98 = x_125;
x_99 = x_129;
x_100 = x_126;
x_101 = x_127;
x_102 = x_128;
x_103 = x_169;
goto block_120;
}
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_130);
lean_dec_ref(x_30);
x_174 = lean_box(0);
x_94 = x_121;
x_95 = x_122;
x_96 = x_123;
x_97 = x_124;
x_98 = x_125;
x_99 = x_129;
x_100 = x_126;
x_101 = x_127;
x_102 = x_128;
x_103 = x_174;
goto block_120;
}
}
block_246:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__16));
lean_inc_ref(x_30);
x_183 = l_Lean_mkConst(x_182, x_30);
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_184 = l_Lean_mkApp3(x_183, x_1, x_39, x_35);
x_185 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__18));
lean_inc_ref(x_30);
x_186 = l_Lean_mkConst(x_185, x_30);
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_187 = l_Lean_mkApp3(x_186, x_1, x_39, x_35);
lean_inc(x_44);
x_188 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(x_44);
if (lean_obj_tag(x_188) == 1)
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_244; 
x_189 = lean_ctor_get(x_188, 0);
x_244 = !lean_is_exclusive(x_188);
if (x_244 == 0)
{
x_190 = x_188;
x_191 = x_244;
goto block_243;
}
else
{
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_box(0);
x_191 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 1)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_214; 
lean_del_object(x_190);
x_193 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_193);
lean_dec(x_189);
x_194 = lean_ctor_get(x_192, 0);
x_214 = !lean_is_exclusive(x_192);
if (x_214 == 0)
{
x_195 = x_192;
x_196 = x_214;
goto block_213;
}
else
{
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_box(0);
x_196 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0);
x_198 = lean_int_dec_eq(x_194, x_197);
lean_dec(x_194);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__20));
lean_inc_ref(x_30);
x_200 = l_Lean_mkConst(x_199, x_30);
x_201 = l_Lean_eagerReflBoolTrue;
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_202 = l_Lean_mkApp5(x_200, x_1, x_39, x_35, x_193, x_201);
if (x_196 == 0)
{
lean_ctor_set(x_195, 0, x_202);
x_203 = x_195;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_202);
x_203 = x_205;
goto block_204;
}
block_204:
{
x_121 = x_176;
x_122 = x_180;
x_123 = x_179;
x_124 = x_187;
x_125 = x_184;
x_126 = x_178;
x_127 = x_181;
x_128 = x_177;
x_129 = x_203;
goto block_175;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec_ref(x_193);
x_206 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__22));
lean_inc_ref(x_30);
x_207 = l_Lean_mkConst(x_206, x_30);
x_208 = l_Lean_eagerReflBoolTrue;
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_209 = l_Lean_mkApp4(x_207, x_1, x_39, x_35, x_208);
if (x_196 == 0)
{
lean_ctor_set(x_195, 0, x_209);
x_210 = x_195;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_209);
x_210 = x_212;
goto block_211;
}
block_211:
{
x_121 = x_176;
x_122 = x_180;
x_123 = x_179;
x_124 = x_187;
x_125 = x_184;
x_126 = x_178;
x_127 = x_181;
x_128 = x_177;
x_129 = x_210;
goto block_175;
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_192);
x_215 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_215);
lean_dec(x_189);
x_216 = l_Lean_Int_mkType;
lean_inc(x_181);
lean_inc_ref(x_180);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc_ref(x_215);
x_217 = l_Lean_Meta_mkSome(x_216, x_215, x_178, x_179, x_180, x_181);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
lean_inc(x_181);
lean_inc_ref(x_180);
lean_inc(x_179);
lean_inc_ref(x_178);
x_219 = l_Lean_Meta_mkEqRefl(x_218, x_178, x_179, x_180, x_181);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__24));
lean_inc_ref(x_30);
x_222 = l_Lean_mkConst(x_221, x_30);
lean_inc(x_35);
lean_inc(x_39);
lean_inc_ref(x_1);
x_223 = l_Lean_mkApp5(x_222, x_1, x_39, x_35, x_215, x_220);
if (x_191 == 0)
{
lean_ctor_set(x_190, 0, x_223);
x_224 = x_190;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_223);
x_224 = x_226;
goto block_225;
}
block_225:
{
x_121 = x_176;
x_122 = x_180;
x_123 = x_179;
x_124 = x_187;
x_125 = x_184;
x_126 = x_178;
x_127 = x_181;
x_128 = x_177;
x_129 = x_224;
goto block_175;
}
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_234; 
lean_dec_ref(x_215);
lean_del_object(x_190);
lean_dec_ref(x_187);
lean_dec_ref(x_184);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_176);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec_ref(x_1);
x_227 = lean_ctor_get(x_219, 0);
x_234 = !lean_is_exclusive(x_219);
if (x_234 == 0)
{
x_228 = x_219;
x_229 = x_234;
goto block_233;
}
else
{
lean_inc(x_227);
lean_dec(x_219);
x_228 = lean_box(0);
x_229 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_230; 
if (x_229 == 0)
{
x_230 = x_228;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_227);
x_230 = x_232;
goto block_231;
}
block_231:
{
return x_230;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_215);
lean_del_object(x_190);
lean_dec_ref(x_187);
lean_dec_ref(x_184);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_176);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_del_object(x_45);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec_ref(x_1);
x_235 = lean_ctor_get(x_217, 0);
x_242 = !lean_is_exclusive(x_217);
if (x_242 == 0)
{
x_236 = x_217;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_217);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
}
}
else
{
lean_object* x_245; 
lean_dec(x_188);
x_245 = lean_box(0);
x_121 = x_176;
x_122 = x_180;
x_123 = x_179;
x_124 = x_187;
x_125 = x_184;
x_126 = x_178;
x_127 = x_181;
x_128 = x_177;
x_129 = x_245;
goto block_175;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_41);
lean_dec(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_270 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_270);
x_271 = x_42;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_270);
x_271 = x_273;
goto block_272;
}
block_272:
{
return x_271;
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_283; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_276 = lean_ctor_get(x_40, 0);
x_283 = !lean_is_exclusive(x_40);
if (x_283 == 0)
{
x_277 = x_40;
x_278 = x_283;
goto block_282;
}
else
{
lean_inc(x_276);
lean_dec(x_40);
x_277 = lean_box(0);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_278 == 0)
{
x_279 = x_277;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_276);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_22);
lean_dec_ref(x_1);
x_286 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f___closed__1));
x_287 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__0___redArg(x_286, x_10);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
x_289 = lean_unbox(x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_dec_ref(x_32);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
goto block_15;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__29);
x_291 = l_Lean_indentExpr(x_32);
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_toIntInterval_x3f_spec__1___redArg(x_286, x_292, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_293) == 0)
{
lean_dec_ref(x_293);
goto block_15;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_301; 
x_294 = lean_ctor_get(x_293, 0);
x_301 = !lean_is_exclusive(x_293);
if (x_301 == 0)
{
x_295 = x_293;
x_296 = x_301;
goto block_300;
}
else
{
lean_inc(x_294);
lean_dec(x_293);
x_295 = lean_box(0);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
if (x_296 == 0)
{
x_297 = x_295;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_294);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_309; 
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_302 = lean_ctor_get(x_33, 0);
x_309 = !lean_is_exclusive(x_33);
if (x_309 == 0)
{
x_303 = x_33;
x_304 = x_309;
goto block_308;
}
else
{
lean_inc(x_302);
lean_dec(x_33);
x_303 = lean_box(0);
x_304 = x_309;
goto block_308;
}
block_308:
{
lean_object* x_305; 
if (x_304 == 0)
{
x_305 = x_303;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_302);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
else
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_317; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_310 = lean_ctor_get(x_27, 0);
x_317 = !lean_is_exclusive(x_27);
if (x_317 == 0)
{
x_311 = x_27;
x_312 = x_317;
goto block_316;
}
else
{
lean_inc(x_310);
lean_dec(x_27);
x_311 = lean_box(0);
x_312 = x_317;
goto block_316;
}
block_316:
{
lean_object* x_313; 
if (x_312 == 0)
{
x_313 = x_311;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_310);
x_313 = x_315;
goto block_314;
}
block_314:
{
return x_313;
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_318 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_318);
x_319 = x_20;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_318);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_331; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_324 = lean_ctor_get(x_18, 0);
x_331 = !lean_is_exclusive(x_18);
if (x_331 == 0)
{
x_325 = x_18;
x_326 = x_331;
goto block_330;
}
else
{
lean_inc(x_324);
lean_dec(x_18);
x_325 = lean_box(0);
x_326 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_327; 
if (x_326 == 0)
{
x_327 = x_325;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_324);
x_327 = x_329;
goto block_328;
}
block_328:
{
return x_327;
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_339; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_332 = lean_ctor_get(x_16, 0);
x_339 = !lean_is_exclusive(x_16);
if (x_339 == 0)
{
x_333 = x_16;
x_334 = x_339;
goto block_338;
}
else
{
lean_inc(x_332);
lean_dec(x_16);
x_333 = lean_box(0);
x_334 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_335; 
if (x_334 == 0)
{
x_335 = x_333;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_332);
x_335 = x_337;
goto block_336;
}
block_336:
{
return x_335;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___boxed), 12, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = 0;
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f_spec__1___redArg(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_ctor_get(x_3, 8);
x_13 = lean_ctor_get(x_3, 9);
x_14 = lean_ctor_get(x_3, 10);
x_15 = lean_ctor_get(x_3, 11);
x_16 = lean_ctor_get(x_3, 12);
x_17 = lean_ctor_get(x_3, 13);
x_18 = lean_ctor_get(x_3, 14);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*23);
x_20 = lean_ctor_get(x_3, 15);
x_21 = lean_ctor_get(x_3, 16);
x_22 = lean_ctor_get(x_3, 17);
x_23 = lean_ctor_get(x_3, 18);
x_24 = lean_ctor_get(x_3, 19);
x_25 = lean_ctor_get(x_3, 20);
x_26 = lean_ctor_get(x_3, 21);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*23 + 1);
x_28 = lean_ctor_get(x_3, 22);
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
x_29 = x_3;
x_30 = x_36;
goto block_35;
}
else
{
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1___redArg(x_23, x_1, x_2);
if (x_30 == 0)
{
lean_ctor_set(x_29, 18, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_6);
lean_ctor_set(x_34, 3, x_7);
lean_ctor_set(x_34, 4, x_8);
lean_ctor_set(x_34, 5, x_9);
lean_ctor_set(x_34, 6, x_10);
lean_ctor_set(x_34, 7, x_11);
lean_ctor_set(x_34, 8, x_12);
lean_ctor_set(x_34, 9, x_13);
lean_ctor_set(x_34, 10, x_14);
lean_ctor_set(x_34, 11, x_15);
lean_ctor_set(x_34, 12, x_16);
lean_ctor_set(x_34, 13, x_17);
lean_ctor_set(x_34, 14, x_18);
lean_ctor_set(x_34, 15, x_20);
lean_ctor_set(x_34, 16, x_21);
lean_ctor_set(x_34, 17, x_22);
lean_ctor_set(x_34, 18, x_31);
lean_ctor_set(x_34, 19, x_24);
lean_ctor_set(x_34, 20, x_25);
lean_ctor_set(x_34, 21, x_26);
lean_ctor_set(x_34, 22, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*23, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*23 + 1, x_27);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_45; 
x_14 = lean_ctor_get(x_13, 0);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
x_15 = x_13;
x_16 = x_45;
goto block_44;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 18);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; 
lean_dec(x_18);
lean_del_object(x_15);
lean_inc(x_2);
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f___lam__0), 3, 2);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_27 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_26, x_25, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_28 = x_27;
x_29 = x_34;
goto block_33;
}
else
{
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_24);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_24);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec(x_24);
x_36 = lean_ctor_get(x_27, 0);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
x_37 = x_27;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_13, 0);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
x_47 = x_13;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_22; 
x_6 = lean_ctor_get(x_5, 0);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
x_7 = x_5;
x_8 = x_22;
goto block_21;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 19);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 2);
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
x_12 = lean_nat_dec_lt(x_1, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_9);
x_13 = l_outOfBounds___redArg(x_11);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_13);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_PersistentArray_get_x21___redArg(x_11, x_9, x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_17);
x_18 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
x_24 = x_5;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_ctor_get(x_3, 8);
x_13 = lean_ctor_get(x_3, 9);
x_14 = lean_ctor_get(x_3, 10);
x_15 = lean_ctor_get(x_3, 11);
x_16 = lean_ctor_get(x_3, 12);
x_17 = lean_ctor_get(x_3, 13);
x_18 = lean_ctor_get(x_3, 14);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*23);
x_20 = lean_ctor_get(x_3, 15);
x_21 = lean_ctor_get(x_3, 16);
x_22 = lean_ctor_get(x_3, 17);
x_23 = lean_ctor_get(x_3, 18);
x_24 = lean_ctor_get(x_3, 19);
x_25 = lean_ctor_get(x_3, 20);
x_26 = lean_ctor_get(x_3, 21);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*23 + 1);
x_28 = lean_ctor_get(x_3, 22);
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
x_29 = x_3;
x_30 = x_36;
goto block_35;
}
else
{
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentArray_modify___redArg(x_24, x_1, x_2);
if (x_30 == 0)
{
lean_ctor_set(x_29, 19, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_6);
lean_ctor_set(x_34, 3, x_7);
lean_ctor_set(x_34, 4, x_8);
lean_ctor_set(x_34, 5, x_9);
lean_ctor_set(x_34, 6, x_10);
lean_ctor_set(x_34, 7, x_11);
lean_ctor_set(x_34, 8, x_12);
lean_ctor_set(x_34, 9, x_13);
lean_ctor_set(x_34, 10, x_14);
lean_ctor_set(x_34, 11, x_15);
lean_ctor_set(x_34, 12, x_16);
lean_ctor_set(x_34, 13, x_17);
lean_ctor_set(x_34, 14, x_18);
lean_ctor_set(x_34, 15, x_20);
lean_ctor_set(x_34, 16, x_21);
lean_ctor_set(x_34, 17, x_22);
lean_ctor_set(x_34, 18, x_23);
lean_ctor_set(x_34, 19, x_31);
lean_ctor_set(x_34, 20, x_25);
lean_ctor_set(x_34, 21, x_26);
lean_ctor_set(x_34, 22, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*23, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*23 + 1, x_27);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_7 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_6, x_5, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_16 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_15, x_14, x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_modifyInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_48; 
x_15 = lean_ctor_get(x_14, 0);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
x_16 = x_14;
x_17 = x_48;
goto block_47;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_42; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
x_19 = x_15;
x_20 = x_42;
goto block_41;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_21; 
x_21 = lean_apply_12(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_22 = lean_ctor_get(x_21, 0);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
x_23 = x_21;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_22);
x_25 = x_19;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_del_object(x_19);
x_33 = lean_ctor_get(x_21, 0);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
x_34 = x_21;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_43);
x_44 = x_16;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_14, 0);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
x_50 = x_14;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_25; 
x_15 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_16 = x_14;
x_17 = x_25;
goto block_24;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_25;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_apply_12(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_20 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_20);
x_21 = x_16;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_14, 0);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_27 = x_14;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__4);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Int_mkType;
x_2 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__5);
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl___closed__6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_13);
lean_dec(x_9);
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__1));
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_inc_ref(x_16);
x_17 = l_Lean_mkConst(x_14, x_16);
lean_inc_ref(x_10);
x_18 = l_Lean_Expr_app___override(x_17, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_19 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_18, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_89; 
x_20 = lean_ctor_get(x_19, 0);
x_89 = !lean_is_exclusive(x_19);
if (x_89 == 0)
{
x_21 = x_19;
x_22 = x_89;
goto block_88;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_83; 
lean_del_object(x_21);
x_23 = lean_ctor_get(x_20, 0);
x_83 = !lean_is_exclusive(x_20);
if (x_83 == 0)
{
x_24 = x_20;
x_25 = x_83;
goto block_82;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__2));
lean_inc_ref(x_16);
x_27 = l_Lean_mkConst(x_26, x_16);
lean_inc_ref(x_12);
lean_inc_ref(x_13);
lean_inc(x_23);
lean_inc_ref(x_10);
x_28 = l_Lean_mkApp4(x_27, x_10, x_23, x_13, x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_28);
x_29 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_28, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_73; 
x_30 = lean_ctor_get(x_29, 0);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
x_31 = x_29;
x_32 = x_73;
goto block_72;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_53; 
lean_dec_ref(x_28);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = lean_ctor_get(x_30, 0);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
x_34 = x_30;
x_35 = x_53;
goto block_52;
}
else
{
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__4));
lean_inc_ref(x_16);
x_37 = l_Lean_mkConst(x_36, x_16);
lean_inc(x_33);
lean_inc(x_23);
lean_inc_ref(x_12);
lean_inc_ref(x_13);
lean_inc_ref(x_10);
x_38 = l_Lean_mkApp5(x_37, x_10, x_13, x_12, x_23, x_33);
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__6));
x_40 = l_Lean_mkConst(x_39, x_16);
x_41 = l_Lean_mkApp5(x_40, x_10, x_13, x_12, x_23, x_33);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_38);
x_42 = x_34;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_38);
x_42 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_43; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_41);
x_43 = x_24;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_41);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_44);
x_45 = x_31;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_54; 
lean_del_object(x_31);
lean_dec(x_30);
lean_del_object(x_24);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_10, x_28, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_54, 0);
lean_dec(x_63);
x_55 = x_54;
x_56 = x_62;
goto block_61;
}
else
{
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7));
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_57);
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
x_64 = lean_ctor_get(x_54, 0);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
x_65 = x_54;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec_ref(x_28);
lean_del_object(x_24);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_74 = lean_ctor_get(x_29, 0);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
x_75 = x_29;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_84 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7));
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_84);
x_85 = x_21;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_90 = lean_ctor_get(x_19, 0);
x_97 = !lean_is_exclusive(x_19);
if (x_97 == 0)
{
x_91 = x_19;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_19);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_98 = lean_ctor_get(x_8, 0);
x_105 = !lean_is_exclusive(x_8);
if (x_105 == 0)
{
x_99 = x_8;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_8);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_usize_shift_right(x_4, x_5);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_28; 
lean_inc_ref(x_6);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_11 = x_3;
x_12 = x_28;
goto block_27;
}
else
{
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_28;
goto block_27;
}
block_27:
{
size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = 1;
x_14 = lean_usize_shift_left(x_13, x_5);
x_15 = lean_usize_sub(x_14, x_13);
x_16 = lean_usize_land(x_4, x_15);
x_17 = 5;
x_18 = lean_usize_sub(x_5, x_17);
x_19 = lean_array_fget(x_6, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_6, x_8, x_20);
x_22 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(x_1, x_2, x_19, x_16, x_18);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_23);
x_24 = x_11;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_usize_to_nat(x_4);
x_32 = lean_array_get_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_79; 
lean_inc_ref(x_30);
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_80);
x_34 = x_3;
x_35 = x_79;
goto block_78;
}
else
{
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_75; 
x_36 = lean_array_fget(x_30, x_31);
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 2);
x_40 = lean_ctor_get(x_36, 3);
x_41 = lean_ctor_get(x_36, 4);
x_42 = lean_ctor_get(x_36, 5);
x_43 = lean_ctor_get(x_36, 6);
x_44 = lean_ctor_get(x_36, 7);
x_45 = lean_ctor_get(x_36, 8);
x_46 = lean_ctor_get(x_36, 9);
x_47 = lean_ctor_get(x_36, 10);
x_48 = lean_ctor_get(x_36, 11);
x_49 = lean_ctor_get(x_36, 12);
x_50 = lean_ctor_get(x_36, 15);
x_51 = lean_ctor_get(x_36, 16);
x_52 = lean_ctor_get(x_36, 17);
x_53 = lean_ctor_get(x_36, 18);
x_54 = lean_ctor_get(x_36, 19);
x_55 = lean_ctor_get(x_36, 20);
x_56 = lean_ctor_get(x_36, 21);
x_57 = lean_ctor_get(x_36, 22);
x_58 = lean_ctor_get(x_36, 23);
x_59 = lean_ctor_get(x_36, 24);
x_60 = lean_ctor_get(x_36, 25);
x_75 = !lean_is_exclusive(x_36);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_36, 14);
lean_dec(x_76);
x_77 = lean_ctor_get(x_36, 13);
lean_dec(x_77);
x_61 = x_36;
x_62 = x_75;
goto block_74;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_61 = lean_box(0);
x_62 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_30, x_31, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_2);
if (x_62 == 0)
{
lean_ctor_set(x_61, 14, x_66);
lean_ctor_set(x_61, 13, x_65);
x_67 = x_61;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_38);
lean_ctor_set(x_73, 2, x_39);
lean_ctor_set(x_73, 3, x_40);
lean_ctor_set(x_73, 4, x_41);
lean_ctor_set(x_73, 5, x_42);
lean_ctor_set(x_73, 6, x_43);
lean_ctor_set(x_73, 7, x_44);
lean_ctor_set(x_73, 8, x_45);
lean_ctor_set(x_73, 9, x_46);
lean_ctor_set(x_73, 10, x_47);
lean_ctor_set(x_73, 11, x_48);
lean_ctor_set(x_73, 12, x_49);
lean_ctor_set(x_73, 13, x_65);
lean_ctor_set(x_73, 14, x_66);
lean_ctor_set(x_73, 15, x_50);
lean_ctor_set(x_73, 16, x_51);
lean_ctor_set(x_73, 17, x_52);
lean_ctor_set(x_73, 18, x_53);
lean_ctor_set(x_73, 19, x_54);
lean_ctor_set(x_73, 20, x_55);
lean_ctor_set(x_73, 21, x_56);
lean_ctor_set(x_73, 22, x_57);
lean_ctor_set(x_73, 23, x_58);
lean_ctor_set(x_73, 24, x_59);
lean_ctor_set(x_73, 25, x_60);
x_67 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_array_fset(x_64, x_31, x_67);
lean_dec(x_31);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_68);
x_69 = x_34;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_68; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get_usize(x_4, 4);
x_10 = lean_ctor_get(x_4, 3);
x_68 = !lean_is_exclusive(x_4);
if (x_68 == 0)
{
x_11 = x_4;
x_12 = x_68;
goto block_67;
}
else
{
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = x_68;
goto block_67;
}
block_67:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_5);
if (x_13 == 0)
{
size_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
x_15 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(x_1, x_2, x_6, x_14, x_9);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_15);
x_16 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_8);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set_usize(x_18, 4, x_9);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_nat_sub(x_5, x_10);
x_20 = lean_array_get_size(x_7);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
if (x_12 == 0)
{
x_22 = x_11;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set_usize(x_24, 4, x_9);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_64; 
x_25 = lean_array_fget(x_7, x_19);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 2);
x_29 = lean_ctor_get(x_25, 3);
x_30 = lean_ctor_get(x_25, 4);
x_31 = lean_ctor_get(x_25, 5);
x_32 = lean_ctor_get(x_25, 6);
x_33 = lean_ctor_get(x_25, 7);
x_34 = lean_ctor_get(x_25, 8);
x_35 = lean_ctor_get(x_25, 9);
x_36 = lean_ctor_get(x_25, 10);
x_37 = lean_ctor_get(x_25, 11);
x_38 = lean_ctor_get(x_25, 12);
x_39 = lean_ctor_get(x_25, 15);
x_40 = lean_ctor_get(x_25, 16);
x_41 = lean_ctor_get(x_25, 17);
x_42 = lean_ctor_get(x_25, 18);
x_43 = lean_ctor_get(x_25, 19);
x_44 = lean_ctor_get(x_25, 20);
x_45 = lean_ctor_get(x_25, 21);
x_46 = lean_ctor_get(x_25, 22);
x_47 = lean_ctor_get(x_25, 23);
x_48 = lean_ctor_get(x_25, 24);
x_49 = lean_ctor_get(x_25, 25);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_25, 14);
lean_dec(x_65);
x_66 = lean_ctor_get(x_25, 13);
lean_dec(x_66);
x_50 = x_25;
x_51 = x_64;
goto block_63;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_50 = lean_box(0);
x_51 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_7, x_19, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
if (x_51 == 0)
{
lean_ctor_set(x_50, 14, x_55);
lean_ctor_set(x_50, 13, x_54);
x_56 = x_50;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_27);
lean_ctor_set(x_62, 2, x_28);
lean_ctor_set(x_62, 3, x_29);
lean_ctor_set(x_62, 4, x_30);
lean_ctor_set(x_62, 5, x_31);
lean_ctor_set(x_62, 6, x_32);
lean_ctor_set(x_62, 7, x_33);
lean_ctor_set(x_62, 8, x_34);
lean_ctor_set(x_62, 9, x_35);
lean_ctor_set(x_62, 10, x_36);
lean_ctor_set(x_62, 11, x_37);
lean_ctor_set(x_62, 12, x_38);
lean_ctor_set(x_62, 13, x_54);
lean_ctor_set(x_62, 14, x_55);
lean_ctor_set(x_62, 15, x_39);
lean_ctor_set(x_62, 16, x_40);
lean_ctor_set(x_62, 17, x_41);
lean_ctor_set(x_62, 18, x_42);
lean_ctor_set(x_62, 19, x_43);
lean_ctor_set(x_62, 20, x_44);
lean_ctor_set(x_62, 21, x_45);
lean_ctor_set(x_62, 22, x_46);
lean_ctor_set(x_62, 23, x_47);
lean_ctor_set(x_62, 24, x_48);
lean_ctor_set(x_62, 25, x_49);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fset(x_53, x_19, x_56);
lean_dec(x_19);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_57);
x_58 = x_11;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_8);
lean_ctor_set(x_60, 3, x_10);
lean_ctor_set_usize(x_60, 4, x_9);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_38; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_ctor_get(x_5, 8);
x_15 = lean_ctor_get(x_5, 9);
x_16 = lean_ctor_get(x_5, 10);
x_17 = lean_ctor_get(x_5, 11);
x_18 = lean_ctor_get(x_5, 12);
x_19 = lean_ctor_get(x_5, 13);
x_20 = lean_ctor_get(x_5, 14);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*23);
x_22 = lean_ctor_get(x_5, 15);
x_23 = lean_ctor_get(x_5, 16);
x_24 = lean_ctor_get(x_5, 17);
x_25 = lean_ctor_get(x_5, 18);
x_26 = lean_ctor_get(x_5, 19);
x_27 = lean_ctor_get(x_5, 20);
x_28 = lean_ctor_get(x_5, 21);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*23 + 1);
x_30 = lean_ctor_get(x_5, 22);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
x_31 = x_5;
x_32 = x_38;
goto block_37;
}
else
{
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0(x_1, x_2, x_3, x_26, x_4);
if (x_32 == 0)
{
lean_ctor_set(x_31, 19, x_33);
x_34 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 2, x_8);
lean_ctor_set(x_36, 3, x_9);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_19);
lean_ctor_set(x_36, 14, x_20);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_33);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*23, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*23 + 1, x_29);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_9 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_10 = x_8;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 13);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_19);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_19);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_19);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_17, 0);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
x_42 = x_17;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_8, 0);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
x_52 = x_8;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_9 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_10 = x_8;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 14);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_17, 0);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
x_42 = x_17;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_8, 0);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
x_52 = x_8;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_13);
lean_dec(x_9);
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__1));
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_inc_ref(x_16);
x_17 = l_Lean_mkConst(x_14, x_16);
lean_inc_ref(x_10);
x_18 = l_Lean_Expr_app___override(x_17, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_19 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_18, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_89; 
x_20 = lean_ctor_get(x_19, 0);
x_89 = !lean_is_exclusive(x_19);
if (x_89 == 0)
{
x_21 = x_19;
x_22 = x_89;
goto block_88;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_83; 
lean_del_object(x_21);
x_23 = lean_ctor_get(x_20, 0);
x_83 = !lean_is_exclusive(x_20);
if (x_83 == 0)
{
x_24 = x_20;
x_25 = x_83;
goto block_82;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__2));
lean_inc_ref(x_16);
x_27 = l_Lean_mkConst(x_26, x_16);
lean_inc_ref(x_12);
lean_inc_ref(x_13);
lean_inc(x_23);
lean_inc_ref(x_10);
x_28 = l_Lean_mkApp4(x_27, x_10, x_23, x_13, x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_28);
x_29 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_28, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_73; 
x_30 = lean_ctor_get(x_29, 0);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
x_31 = x_29;
x_32 = x_73;
goto block_72;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_53; 
lean_dec_ref(x_28);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = lean_ctor_get(x_30, 0);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
x_34 = x_30;
x_35 = x_53;
goto block_52;
}
else
{
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__4));
lean_inc_ref(x_16);
x_37 = l_Lean_mkConst(x_36, x_16);
lean_inc(x_33);
lean_inc(x_23);
lean_inc_ref(x_12);
lean_inc_ref(x_13);
lean_inc_ref(x_10);
x_38 = l_Lean_mkApp5(x_37, x_10, x_13, x_12, x_23, x_33);
x_39 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___closed__6));
x_40 = l_Lean_mkConst(x_39, x_16);
x_41 = l_Lean_mkApp5(x_40, x_10, x_13, x_12, x_23, x_33);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_38);
x_42 = x_34;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_38);
x_42 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_43; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_41);
x_43 = x_24;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_41);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_44);
x_45 = x_31;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_54; 
lean_del_object(x_31);
lean_dec(x_30);
lean_del_object(x_24);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_10, x_28, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_54, 0);
lean_dec(x_63);
x_55 = x_54;
x_56 = x_62;
goto block_61;
}
else
{
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7));
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_57);
x_58 = x_55;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
x_64 = lean_ctor_get(x_54, 0);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
x_65 = x_54;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec_ref(x_28);
lean_del_object(x_24);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_74 = lean_ctor_get(x_29, 0);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
x_75 = x_29;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_84 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLE___redArg___closed__7));
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_84);
x_85 = x_21;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_16);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_90 = lean_ctor_get(x_19, 0);
x_97 = !lean_is_exclusive(x_19);
if (x_97 == 0)
{
x_91 = x_19;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_19);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_98 = lean_ctor_get(x_8, 0);
x_105 = !lean_is_exclusive(x_8);
if (x_105 == 0)
{
x_99 = x_8;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_8);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_usize_shift_right(x_4, x_5);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_28; 
lean_inc_ref(x_6);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_11 = x_3;
x_12 = x_28;
goto block_27;
}
else
{
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_28;
goto block_27;
}
block_27:
{
size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = 1;
x_14 = lean_usize_shift_left(x_13, x_5);
x_15 = lean_usize_sub(x_14, x_13);
x_16 = lean_usize_land(x_4, x_15);
x_17 = 5;
x_18 = lean_usize_sub(x_5, x_17);
x_19 = lean_array_fget(x_6, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_6, x_8, x_20);
x_22 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(x_1, x_2, x_19, x_16, x_18);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_23);
x_24 = x_11;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_usize_to_nat(x_4);
x_32 = lean_array_get_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_79; 
lean_inc_ref(x_30);
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_80);
x_34 = x_3;
x_35 = x_79;
goto block_78;
}
else
{
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_75; 
x_36 = lean_array_fget(x_30, x_31);
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 2);
x_40 = lean_ctor_get(x_36, 3);
x_41 = lean_ctor_get(x_36, 4);
x_42 = lean_ctor_get(x_36, 5);
x_43 = lean_ctor_get(x_36, 6);
x_44 = lean_ctor_get(x_36, 7);
x_45 = lean_ctor_get(x_36, 8);
x_46 = lean_ctor_get(x_36, 9);
x_47 = lean_ctor_get(x_36, 10);
x_48 = lean_ctor_get(x_36, 11);
x_49 = lean_ctor_get(x_36, 12);
x_50 = lean_ctor_get(x_36, 13);
x_51 = lean_ctor_get(x_36, 14);
x_52 = lean_ctor_get(x_36, 17);
x_53 = lean_ctor_get(x_36, 18);
x_54 = lean_ctor_get(x_36, 19);
x_55 = lean_ctor_get(x_36, 20);
x_56 = lean_ctor_get(x_36, 21);
x_57 = lean_ctor_get(x_36, 22);
x_58 = lean_ctor_get(x_36, 23);
x_59 = lean_ctor_get(x_36, 24);
x_60 = lean_ctor_get(x_36, 25);
x_75 = !lean_is_exclusive(x_36);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_36, 16);
lean_dec(x_76);
x_77 = lean_ctor_get(x_36, 15);
lean_dec(x_77);
x_61 = x_36;
x_62 = x_75;
goto block_74;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_61 = lean_box(0);
x_62 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_30, x_31, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_2);
if (x_62 == 0)
{
lean_ctor_set(x_61, 16, x_66);
lean_ctor_set(x_61, 15, x_65);
x_67 = x_61;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_38);
lean_ctor_set(x_73, 2, x_39);
lean_ctor_set(x_73, 3, x_40);
lean_ctor_set(x_73, 4, x_41);
lean_ctor_set(x_73, 5, x_42);
lean_ctor_set(x_73, 6, x_43);
lean_ctor_set(x_73, 7, x_44);
lean_ctor_set(x_73, 8, x_45);
lean_ctor_set(x_73, 9, x_46);
lean_ctor_set(x_73, 10, x_47);
lean_ctor_set(x_73, 11, x_48);
lean_ctor_set(x_73, 12, x_49);
lean_ctor_set(x_73, 13, x_50);
lean_ctor_set(x_73, 14, x_51);
lean_ctor_set(x_73, 15, x_65);
lean_ctor_set(x_73, 16, x_66);
lean_ctor_set(x_73, 17, x_52);
lean_ctor_set(x_73, 18, x_53);
lean_ctor_set(x_73, 19, x_54);
lean_ctor_set(x_73, 20, x_55);
lean_ctor_set(x_73, 21, x_56);
lean_ctor_set(x_73, 22, x_57);
lean_ctor_set(x_73, 23, x_58);
lean_ctor_set(x_73, 24, x_59);
lean_ctor_set(x_73, 25, x_60);
x_67 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_array_fset(x_64, x_31, x_67);
lean_dec(x_31);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_68);
x_69 = x_34;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_68; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get_usize(x_4, 4);
x_10 = lean_ctor_get(x_4, 3);
x_68 = !lean_is_exclusive(x_4);
if (x_68 == 0)
{
x_11 = x_4;
x_12 = x_68;
goto block_67;
}
else
{
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = x_68;
goto block_67;
}
block_67:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_5);
if (x_13 == 0)
{
size_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
x_15 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(x_1, x_2, x_6, x_14, x_9);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_15);
x_16 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_8);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set_usize(x_18, 4, x_9);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_nat_sub(x_5, x_10);
x_20 = lean_array_get_size(x_7);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
if (x_12 == 0)
{
x_22 = x_11;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set_usize(x_24, 4, x_9);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_64; 
x_25 = lean_array_fget(x_7, x_19);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 2);
x_29 = lean_ctor_get(x_25, 3);
x_30 = lean_ctor_get(x_25, 4);
x_31 = lean_ctor_get(x_25, 5);
x_32 = lean_ctor_get(x_25, 6);
x_33 = lean_ctor_get(x_25, 7);
x_34 = lean_ctor_get(x_25, 8);
x_35 = lean_ctor_get(x_25, 9);
x_36 = lean_ctor_get(x_25, 10);
x_37 = lean_ctor_get(x_25, 11);
x_38 = lean_ctor_get(x_25, 12);
x_39 = lean_ctor_get(x_25, 13);
x_40 = lean_ctor_get(x_25, 14);
x_41 = lean_ctor_get(x_25, 17);
x_42 = lean_ctor_get(x_25, 18);
x_43 = lean_ctor_get(x_25, 19);
x_44 = lean_ctor_get(x_25, 20);
x_45 = lean_ctor_get(x_25, 21);
x_46 = lean_ctor_get(x_25, 22);
x_47 = lean_ctor_get(x_25, 23);
x_48 = lean_ctor_get(x_25, 24);
x_49 = lean_ctor_get(x_25, 25);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_25, 16);
lean_dec(x_65);
x_66 = lean_ctor_get(x_25, 15);
lean_dec(x_66);
x_50 = x_25;
x_51 = x_64;
goto block_63;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_50 = lean_box(0);
x_51 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_7, x_19, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_2);
if (x_51 == 0)
{
lean_ctor_set(x_50, 16, x_55);
lean_ctor_set(x_50, 15, x_54);
x_56 = x_50;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_27);
lean_ctor_set(x_62, 2, x_28);
lean_ctor_set(x_62, 3, x_29);
lean_ctor_set(x_62, 4, x_30);
lean_ctor_set(x_62, 5, x_31);
lean_ctor_set(x_62, 6, x_32);
lean_ctor_set(x_62, 7, x_33);
lean_ctor_set(x_62, 8, x_34);
lean_ctor_set(x_62, 9, x_35);
lean_ctor_set(x_62, 10, x_36);
lean_ctor_set(x_62, 11, x_37);
lean_ctor_set(x_62, 12, x_38);
lean_ctor_set(x_62, 13, x_39);
lean_ctor_set(x_62, 14, x_40);
lean_ctor_set(x_62, 15, x_54);
lean_ctor_set(x_62, 16, x_55);
lean_ctor_set(x_62, 17, x_41);
lean_ctor_set(x_62, 18, x_42);
lean_ctor_set(x_62, 19, x_43);
lean_ctor_set(x_62, 20, x_44);
lean_ctor_set(x_62, 21, x_45);
lean_ctor_set(x_62, 22, x_46);
lean_ctor_set(x_62, 23, x_47);
lean_ctor_set(x_62, 24, x_48);
lean_ctor_set(x_62, 25, x_49);
x_56 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fset(x_53, x_19, x_56);
lean_dec(x_19);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_57);
x_58 = x_11;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_8);
lean_ctor_set(x_60, 3, x_10);
lean_ctor_set_usize(x_60, 4, x_9);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_38; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_ctor_get(x_5, 8);
x_15 = lean_ctor_get(x_5, 9);
x_16 = lean_ctor_get(x_5, 10);
x_17 = lean_ctor_get(x_5, 11);
x_18 = lean_ctor_get(x_5, 12);
x_19 = lean_ctor_get(x_5, 13);
x_20 = lean_ctor_get(x_5, 14);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*23);
x_22 = lean_ctor_get(x_5, 15);
x_23 = lean_ctor_get(x_5, 16);
x_24 = lean_ctor_get(x_5, 17);
x_25 = lean_ctor_get(x_5, 18);
x_26 = lean_ctor_get(x_5, 19);
x_27 = lean_ctor_get(x_5, 20);
x_28 = lean_ctor_get(x_5, 21);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*23 + 1);
x_30 = lean_ctor_get(x_5, 22);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
x_31 = x_5;
x_32 = x_38;
goto block_37;
}
else
{
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0(x_1, x_2, x_3, x_26, x_4);
if (x_32 == 0)
{
lean_ctor_set(x_31, 19, x_33);
x_34 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 2, x_8);
lean_ctor_set(x_36, 3, x_9);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_11);
lean_ctor_set(x_36, 6, x_12);
lean_ctor_set(x_36, 7, x_13);
lean_ctor_set(x_36, 8, x_14);
lean_ctor_set(x_36, 9, x_15);
lean_ctor_set(x_36, 10, x_16);
lean_ctor_set(x_36, 11, x_17);
lean_ctor_set(x_36, 12, x_18);
lean_ctor_set(x_36, 13, x_19);
lean_ctor_set(x_36, 14, x_20);
lean_ctor_set(x_36, 15, x_22);
lean_ctor_set(x_36, 16, x_23);
lean_ctor_set(x_36, 17, x_24);
lean_ctor_set(x_36, 18, x_25);
lean_ctor_set(x_36, 19, x_33);
lean_ctor_set(x_36, 20, x_27);
lean_ctor_set(x_36, 21, x_28);
lean_ctor_set(x_36, 22, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*23, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*23 + 1, x_29);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_9 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_10 = x_8;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 15);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_19);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_19);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_19);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_17, 0);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
x_42 = x_17;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_8, 0);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
x_52 = x_8;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_9 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_10 = x_8;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 16);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfLT___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_17, 0);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
x_42 = x_17;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_8, 0);
x_58 = !lean_is_exclusive(x_8);
if (x_58 == 0)
{
x_52 = x_8;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_97; 
x_12 = lean_ctor_get(x_11, 0);
x_97 = !lean_is_exclusive(x_11);
if (x_97 == 0)
{
x_13 = x_11;
x_14 = x_97;
goto block_96;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_97;
goto block_96;
}
block_96:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_del_object(x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__4));
x_17 = l_Lean_Name_append(x_16, x_2);
lean_inc(x_17);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl(x_17, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_4, x_5, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 3);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_inc_ref(x_26);
x_27 = l_Lean_mkConst(x_17, x_26);
lean_inc_ref(x_23);
lean_inc_ref(x_24);
lean_inc(x_15);
lean_inc_ref(x_21);
x_28 = l_Lean_mkApp4(x_27, x_21, x_15, x_24, x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_28);
x_29 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_28, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_57; 
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_30, 0);
x_57 = !lean_is_exclusive(x_30);
if (x_57 == 0)
{
x_32 = x_30;
x_33 = x_57;
goto block_56;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_34; 
lean_inc(x_3);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_checkDecl(x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_34, 0);
lean_dec(x_47);
x_35 = x_34;
x_36 = x_46;
goto block_45;
}
else
{
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_mkConst(x_3, x_26);
x_38 = l_Lean_mkApp5(x_37, x_21, x_24, x_23, x_15, x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_38);
x_39 = x_32;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_39);
x_40 = x_35;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_del_object(x_32);
lean_dec(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_15);
lean_dec(x_3);
x_48 = lean_ctor_get(x_34, 0);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
x_49 = x_34;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_30);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_15);
lean_dec(x_3);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_21, x_28, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; uint8_t x_66; 
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_58, 0);
lean_dec(x_67);
x_59 = x_58;
x_60 = x_66;
goto block_65;
}
else
{
lean_dec(x_58);
x_59 = lean_box(0);
x_60 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_61);
x_62 = x_59;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
x_68 = lean_ctor_get(x_58, 0);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
x_69 = x_58;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
return x_29;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_76 = lean_ctor_get(x_19, 0);
x_83 = !lean_is_exclusive(x_19);
if (x_83 == 0)
{
x_77 = x_19;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_19);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_84 = lean_ctor_get(x_18, 0);
x_91 = !lean_is_exclusive(x_18);
if (x_91 == 0)
{
x_85 = x_18;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_18);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_92);
x_93 = x_13;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_3, x_4, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_1);
x_16 = l_Lean_mkConst(x_1, x_15);
x_17 = l_Lean_Expr_app___override(x_16, x_12);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__1));
x_13 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__2);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_mkConst(x_12, x_17);
x_19 = l_Lean_Nat_mkType;
lean_inc_ref(x_10);
x_20 = l_Lean_mkApp3(x_18, x_10, x_19, x_10);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__4));
x_22 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___closed__6));
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThmCore_x3f___redArg(x_20, x_21, x_22, x_1, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_8, 0);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
x_25 = x_8;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_101; 
x_11 = lean_ctor_get(x_10, 0);
x_101 = !lean_is_exclusive(x_10);
if (x_101 == 0)
{
x_12 = x_10;
x_13 = x_101;
goto block_100;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_101;
goto block_100;
}
block_100:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_del_object(x_12);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_st_ref_get(x_8);
lean_dec(x_8);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_3, x_4, x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_87; 
x_17 = lean_ctor_get(x_16, 0);
x_87 = !lean_is_exclusive(x_16);
if (x_87 == 0)
{
x_18 = x_16;
x_19 = x_87;
goto block_86;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_60; lean_object* x_61; uint8_t x_62; uint8_t x_71; lean_object* x_72; uint8_t x_75; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_28);
lean_dec(x_15);
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__1));
lean_inc(x_2);
x_30 = l_Lean_Name_append(x_2, x_29);
x_31 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_17, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_17, 5);
lean_inc(x_35);
lean_dec(x_17);
x_36 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__3));
lean_inc(x_2);
x_37 = l_Lean_Name_append(x_2, x_36);
x_38 = l_Lean_Expr_appFn_x21(x_14);
x_39 = l_Lean_Expr_appArg_x21(x_38);
lean_dec_ref(x_38);
x_40 = l_Lean_Expr_appArg_x21(x_14);
x_41 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__5));
x_42 = l_Lean_Name_append(x_2, x_41);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_isFinite(x_35);
lean_dec(x_35);
if (x_54 == 0)
{
x_75 = x_54;
goto block_84;
}
else
{
uint8_t x_85; 
lean_inc(x_30);
lean_inc_ref(x_28);
x_85 = l_Lean_Environment_contains(x_28, x_30, x_54);
x_75 = x_85;
goto block_84;
}
block_27:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_23);
x_24 = x_18;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
block_53:
{
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
x_46 = lean_box(0);
x_20 = x_43;
x_21 = x_44;
x_22 = x_46;
goto block_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_32);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_mkConst(x_42, x_48);
x_50 = l_Lean_eagerReflBoolTrue;
x_51 = l_Lean_mkApp6(x_49, x_31, x_34, x_33, x_39, x_40, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_20 = x_43;
x_21 = x_44;
x_22 = x_52;
goto block_27;
}
}
block_59:
{
if (x_54 == 0)
{
lean_dec_ref(x_28);
x_43 = x_57;
x_44 = x_56;
x_45 = x_54;
goto block_53;
}
else
{
uint8_t x_58; 
lean_inc(x_42);
x_58 = l_Lean_Environment_contains(x_28, x_42, x_55);
x_43 = x_57;
x_44 = x_56;
x_45 = x_58;
goto block_53;
}
}
block_70:
{
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_37);
x_63 = lean_box(0);
x_55 = x_60;
x_56 = x_61;
x_57 = x_63;
goto block_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_box(0);
lean_inc(x_32);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_32);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_mkConst(x_37, x_65);
x_67 = l_Lean_eagerReflBoolTrue;
lean_inc_ref(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_33);
lean_inc_ref(x_34);
lean_inc_ref(x_31);
x_68 = l_Lean_mkApp6(x_66, x_31, x_34, x_33, x_39, x_40, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_55 = x_60;
x_56 = x_61;
x_57 = x_69;
goto block_59;
}
}
block_74:
{
if (x_54 == 0)
{
x_60 = x_71;
x_61 = x_72;
x_62 = x_54;
goto block_70;
}
else
{
uint8_t x_73; 
lean_inc(x_37);
lean_inc_ref(x_28);
x_73 = l_Lean_Environment_contains(x_28, x_37, x_71);
x_60 = x_71;
x_61 = x_72;
x_62 = x_73;
goto block_70;
}
}
block_84:
{
uint8_t x_76; 
x_76 = 1;
if (x_75 == 0)
{
lean_object* x_77; 
lean_dec(x_30);
x_77 = lean_box(0);
x_71 = x_76;
x_72 = x_77;
goto block_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_box(0);
lean_inc(x_32);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_mkConst(x_30, x_79);
x_81 = l_Lean_eagerReflBoolTrue;
lean_inc_ref(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_33);
lean_inc_ref(x_34);
lean_inc_ref(x_31);
x_82 = l_Lean_mkApp6(x_80, x_31, x_34, x_33, x_39, x_40, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_71 = x_76;
x_72 = x_83;
goto block_74;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_15);
lean_dec_ref(x_11);
lean_dec(x_2);
x_88 = lean_ctor_get(x_16, 0);
x_95 = !lean_is_exclusive(x_16);
if (x_95 == 0)
{
x_89 = x_16;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_16);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_96 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___closed__6));
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_96);
x_97 = x_12;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_96);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_102 = lean_ctor_get(x_10, 0);
x_109 = !lean_is_exclusive(x_10);
if (x_109 == 0)
{
x_103 = x_10;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_10);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 18);
x_54 = lean_ctor_get(x_35, 19);
x_55 = lean_ctor_get(x_35, 20);
x_56 = lean_ctor_get(x_35, 21);
x_57 = lean_ctor_get(x_35, 22);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 17);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 17, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_65);
lean_ctor_set(x_72, 18, x_53);
lean_ctor_set(x_72, 19, x_54);
lean_ctor_set(x_72, 20, x_55);
lean_ctor_set(x_72, 21, x_56);
lean_ctor_set(x_72, 22, x_57);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 18);
x_43 = lean_ctor_get(x_24, 19);
x_44 = lean_ctor_get(x_24, 20);
x_45 = lean_ctor_get(x_24, 21);
x_46 = lean_ctor_get(x_24, 22);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 17);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 17, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_54);
lean_ctor_set(x_61, 18, x_42);
lean_ctor_set(x_61, 19, x_43);
lean_ctor_set(x_61, 20, x_44);
lean_ctor_set(x_61, 21, x_45);
lean_ctor_set(x_61, 22, x_46);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 17);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getAddThms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getAddThms_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 19);
x_55 = lean_ctor_get(x_35, 20);
x_56 = lean_ctor_get(x_35, 21);
x_57 = lean_ctor_get(x_35, 22);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 18);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 18, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_65);
lean_ctor_set(x_72, 19, x_54);
lean_ctor_set(x_72, 20, x_55);
lean_ctor_set(x_72, 21, x_56);
lean_ctor_set(x_72, 22, x_57);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 19);
x_44 = lean_ctor_get(x_24, 20);
x_45 = lean_ctor_get(x_24, 21);
x_46 = lean_ctor_get(x_24, 22);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 18);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 18, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_54);
lean_ctor_set(x_61, 19, x_43);
lean_ctor_set(x_61, 20, x_44);
lean_ctor_set(x_61, 21, x_45);
lean_ctor_set(x_61, 22, x_46);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 18);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkBinOpThms___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getMulThms(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getMulThms_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 20);
x_56 = lean_ctor_get(x_35, 21);
x_57 = lean_ctor_get(x_35, 22);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 19);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 19, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_65);
lean_ctor_set(x_72, 20, x_55);
lean_ctor_set(x_72, 21, x_56);
lean_ctor_set(x_72, 22, x_57);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 20);
x_45 = lean_ctor_get(x_24, 21);
x_46 = lean_ctor_get(x_24, 22);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 19);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 19, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_54);
lean_ctor_set(x_61, 20, x_44);
lean_ctor_set(x_61, 21, x_45);
lean_ctor_set(x_61, 22, x_46);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 19);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 21);
x_57 = lean_ctor_get(x_35, 22);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 20);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 20, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_65);
lean_ctor_set(x_72, 21, x_56);
lean_ctor_set(x_72, 22, x_57);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 21);
x_46 = lean_ctor_get(x_24, 22);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 20);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 20, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_54);
lean_ctor_set(x_61, 21, x_45);
lean_ctor_set(x_61, 22, x_46);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 20);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 20);
x_57 = lean_ctor_get(x_35, 22);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 21);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 21, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_56);
lean_ctor_set(x_72, 21, x_65);
lean_ctor_set(x_72, 22, x_57);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 20);
x_46 = lean_ctor_get(x_24, 22);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 21);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 21, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_45);
lean_ctor_set(x_61, 21, x_54);
lean_ctor_set(x_61, 22, x_46);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 21);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 20);
x_57 = lean_ctor_get(x_35, 21);
x_58 = lean_ctor_get(x_35, 23);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 22);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 22, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_56);
lean_ctor_set(x_72, 21, x_57);
lean_ctor_set(x_72, 22, x_65);
lean_ctor_set(x_72, 23, x_58);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 20);
x_46 = lean_ctor_get(x_24, 21);
x_47 = lean_ctor_get(x_24, 23);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 22);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 22, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_45);
lean_ctor_set(x_61, 21, x_46);
lean_ctor_set(x_61, 22, x_54);
lean_ctor_set(x_61, 23, x_47);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 22);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 20);
x_57 = lean_ctor_get(x_35, 21);
x_58 = lean_ctor_get(x_35, 22);
x_59 = lean_ctor_get(x_35, 24);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 23);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 23, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_56);
lean_ctor_set(x_72, 21, x_57);
lean_ctor_set(x_72, 22, x_58);
lean_ctor_set(x_72, 23, x_65);
lean_ctor_set(x_72, 24, x_59);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 20);
x_46 = lean_ctor_get(x_24, 21);
x_47 = lean_ctor_get(x_24, 22);
x_48 = lean_ctor_get(x_24, 24);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 23);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 23, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_45);
lean_ctor_set(x_61, 21, x_46);
lean_ctor_set(x_61, 22, x_47);
lean_ctor_set(x_61, 23, x_54);
lean_ctor_set(x_61, 24, x_48);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_40; 
x_9 = lean_ctor_get(x_8, 0);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
x_10 = x_8;
x_11 = x_40;
goto block_39;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 23);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkPowThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_22 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_21, x_20, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_23 = x_22;
x_24 = x_29;
goto block_28;
}
else
{
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_18);
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_18);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_18);
x_31 = lean_ctor_get(x_22, 0);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
x_32 = x_22;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_dec(x_1);
return x_17;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_8, 0);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
x_42 = x_8;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 20);
x_57 = lean_ctor_get(x_35, 21);
x_58 = lean_ctor_get(x_35, 22);
x_59 = lean_ctor_get(x_35, 23);
x_60 = lean_ctor_get(x_35, 25);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 24);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 24, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_56);
lean_ctor_set(x_72, 21, x_57);
lean_ctor_set(x_72, 22, x_58);
lean_ctor_set(x_72, 23, x_59);
lean_ctor_set(x_72, 24, x_65);
lean_ctor_set(x_72, 25, x_60);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 20);
x_46 = lean_ctor_get(x_24, 21);
x_47 = lean_ctor_get(x_24, 22);
x_48 = lean_ctor_get(x_24, 23);
x_49 = lean_ctor_get(x_24, 25);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 24);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 24, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_45);
lean_ctor_set(x_61, 21, x_46);
lean_ctor_set(x_61, 22, x_47);
lean_ctor_set(x_61, 23, x_48);
lean_ctor_set(x_61, 24, x_54);
lean_ctor_set(x_61, 25, x_49);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 24);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__1));
x_18 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___closed__3));
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkSimpleOpThm_x3f___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_1);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_24 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_23, x_22, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_25 = x_24;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_20);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_24, 0);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
x_34 = x_24;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_dec(x_1);
return x_19;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_8, 0);
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
x_44 = x_8;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_13);
lean_dec(x_9);
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__1));
x_15 = 0;
x_16 = lean_box(0);
x_17 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__4);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__6));
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_16);
lean_inc_ref(x_19);
x_20 = l_Lean_mkConst(x_18, x_19);
x_21 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__7);
lean_inc_ref(x_10);
x_22 = l_Lean_mkAppB(x_20, x_10, x_21);
x_23 = l_Lean_mkForall(x_14, x_15, x_17, x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
x_24 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_23, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__8));
lean_inc_ref(x_19);
x_28 = l_Lean_mkConst(x_27, x_19);
lean_inc_ref(x_12);
lean_inc_ref(x_13);
lean_inc(x_26);
lean_inc_ref(x_10);
x_29 = l_Lean_mkApp4(x_28, x_10, x_26, x_13, x_12);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_29);
x_30 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_29, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_67; 
x_31 = lean_ctor_get(x_30, 0);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
x_32 = x_30;
x_33 = x_67;
goto block_66;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_67;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_47; 
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_34 = lean_ctor_get(x_31, 0);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
x_35 = x_31;
x_36 = x_47;
goto block_46;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__10));
x_38 = l_Lean_mkConst(x_37, x_19);
x_39 = l_Lean_mkApp5(x_38, x_10, x_13, x_12, x_26, x_34);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_39);
x_40 = x_35;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_39);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_40);
x_41 = x_32;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_object* x_48; 
lean_del_object(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_10, x_29, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_48, 0);
lean_dec(x_57);
x_49 = x_48;
x_50 = x_56;
goto block_55;
}
else
{
lean_dec(x_48);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
x_58 = lean_ctor_get(x_48, 0);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
x_59 = x_48;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_30;
}
}
else
{
lean_object* x_68; 
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter(x_10, x_23, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; uint8_t x_76; 
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_68, 0);
lean_dec(x_77);
x_69 = x_68;
x_70 = x_76;
goto block_75;
}
else
{
lean_dec(x_68);
x_69 = lean_box(0);
x_70 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
if (x_70 == 0)
{
lean_ctor_set(x_69, 0, x_71);
x_72 = x_69;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_78 = lean_ctor_get(x_68, 0);
x_85 = !lean_is_exclusive(x_68);
if (x_85 == 0)
{
x_79 = x_68;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_24;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_86 = lean_ctor_get(x_8, 0);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
x_87 = x_8;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_8);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_27; 
lean_inc_ref(x_5);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_10 = x_2;
x_11 = x_27;
goto block_26;
}
else
{
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = x_27;
goto block_26;
}
block_26:
{
size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_usize_to_nat(x_3);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_77; 
lean_inc_ref(x_29);
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
x_33 = x_2;
x_34 = x_77;
goto block_76;
}
else
{
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_74; 
x_35 = lean_array_fget(x_29, x_30);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 2);
x_39 = lean_ctor_get(x_35, 3);
x_40 = lean_ctor_get(x_35, 4);
x_41 = lean_ctor_get(x_35, 5);
x_42 = lean_ctor_get(x_35, 6);
x_43 = lean_ctor_get(x_35, 7);
x_44 = lean_ctor_get(x_35, 8);
x_45 = lean_ctor_get(x_35, 9);
x_46 = lean_ctor_get(x_35, 10);
x_47 = lean_ctor_get(x_35, 11);
x_48 = lean_ctor_get(x_35, 12);
x_49 = lean_ctor_get(x_35, 13);
x_50 = lean_ctor_get(x_35, 14);
x_51 = lean_ctor_get(x_35, 15);
x_52 = lean_ctor_get(x_35, 16);
x_53 = lean_ctor_get(x_35, 17);
x_54 = lean_ctor_get(x_35, 18);
x_55 = lean_ctor_get(x_35, 19);
x_56 = lean_ctor_get(x_35, 20);
x_57 = lean_ctor_get(x_35, 21);
x_58 = lean_ctor_get(x_35, 22);
x_59 = lean_ctor_get(x_35, 23);
x_60 = lean_ctor_get(x_35, 24);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_35, 25);
lean_dec(x_75);
x_61 = x_35;
x_62 = x_74;
goto block_73;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_61 = lean_box(0);
x_62 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_fset(x_29, x_30, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_1);
if (x_62 == 0)
{
lean_ctor_set(x_61, 25, x_65);
x_66 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_38);
lean_ctor_set(x_72, 3, x_39);
lean_ctor_set(x_72, 4, x_40);
lean_ctor_set(x_72, 5, x_41);
lean_ctor_set(x_72, 6, x_42);
lean_ctor_set(x_72, 7, x_43);
lean_ctor_set(x_72, 8, x_44);
lean_ctor_set(x_72, 9, x_45);
lean_ctor_set(x_72, 10, x_46);
lean_ctor_set(x_72, 11, x_47);
lean_ctor_set(x_72, 12, x_48);
lean_ctor_set(x_72, 13, x_49);
lean_ctor_set(x_72, 14, x_50);
lean_ctor_set(x_72, 15, x_51);
lean_ctor_set(x_72, 16, x_52);
lean_ctor_set(x_72, 17, x_53);
lean_ctor_set(x_72, 18, x_54);
lean_ctor_set(x_72, 19, x_55);
lean_ctor_set(x_72, 20, x_56);
lean_ctor_set(x_72, 21, x_57);
lean_ctor_set(x_72, 22, x_58);
lean_ctor_set(x_72, 23, x_59);
lean_ctor_set(x_72, 24, x_60);
lean_ctor_set(x_72, 25, x_65);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fset(x_64, x_30, x_66);
lean_dec(x_30);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_67);
x_68 = x_33;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
x_10 = x_3;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_4);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(x_1, x_5, x_13, x_8);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_usize(x_17, 4, x_8);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_nat_sub(x_4, x_9);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_1);
if (x_11 == 0)
{
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set_usize(x_23, 4, x_8);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_63; 
x_24 = lean_array_fget(x_6, x_18);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 2);
x_28 = lean_ctor_get(x_24, 3);
x_29 = lean_ctor_get(x_24, 4);
x_30 = lean_ctor_get(x_24, 5);
x_31 = lean_ctor_get(x_24, 6);
x_32 = lean_ctor_get(x_24, 7);
x_33 = lean_ctor_get(x_24, 8);
x_34 = lean_ctor_get(x_24, 9);
x_35 = lean_ctor_get(x_24, 10);
x_36 = lean_ctor_get(x_24, 11);
x_37 = lean_ctor_get(x_24, 12);
x_38 = lean_ctor_get(x_24, 13);
x_39 = lean_ctor_get(x_24, 14);
x_40 = lean_ctor_get(x_24, 15);
x_41 = lean_ctor_get(x_24, 16);
x_42 = lean_ctor_get(x_24, 17);
x_43 = lean_ctor_get(x_24, 18);
x_44 = lean_ctor_get(x_24, 19);
x_45 = lean_ctor_get(x_24, 20);
x_46 = lean_ctor_get(x_24, 21);
x_47 = lean_ctor_get(x_24, 22);
x_48 = lean_ctor_get(x_24, 23);
x_49 = lean_ctor_get(x_24, 24);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_24, 25);
lean_dec(x_64);
x_50 = x_24;
x_51 = x_63;
goto block_62;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = lean_array_fset(x_6, x_18, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_1);
if (x_51 == 0)
{
lean_ctor_set(x_50, 25, x_54);
x_55 = x_50;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_26);
lean_ctor_set(x_61, 2, x_27);
lean_ctor_set(x_61, 3, x_28);
lean_ctor_set(x_61, 4, x_29);
lean_ctor_set(x_61, 5, x_30);
lean_ctor_set(x_61, 6, x_31);
lean_ctor_set(x_61, 7, x_32);
lean_ctor_set(x_61, 8, x_33);
lean_ctor_set(x_61, 9, x_34);
lean_ctor_set(x_61, 10, x_35);
lean_ctor_set(x_61, 11, x_36);
lean_ctor_set(x_61, 12, x_37);
lean_ctor_set(x_61, 13, x_38);
lean_ctor_set(x_61, 14, x_39);
lean_ctor_set(x_61, 15, x_40);
lean_ctor_set(x_61, 16, x_41);
lean_ctor_set(x_61, 17, x_42);
lean_ctor_set(x_61, 18, x_43);
lean_ctor_set(x_61, 19, x_44);
lean_ctor_set(x_61, 20, x_45);
lean_ctor_set(x_61, 21, x_46);
lean_ctor_set(x_61, 22, x_47);
lean_ctor_set(x_61, 23, x_48);
lean_ctor_set(x_61, 24, x_49);
lean_ctor_set(x_61, 25, x_54);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fset(x_53, x_18, x_55);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_56);
x_57 = x_10;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_7);
lean_ctor_set(x_59, 3, x_9);
lean_ctor_set_usize(x_59, 4, x_8);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_ctor_get(x_4, 8);
x_14 = lean_ctor_get(x_4, 9);
x_15 = lean_ctor_get(x_4, 10);
x_16 = lean_ctor_get(x_4, 11);
x_17 = lean_ctor_get(x_4, 12);
x_18 = lean_ctor_get(x_4, 13);
x_19 = lean_ctor_get(x_4, 14);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*23);
x_21 = lean_ctor_get(x_4, 15);
x_22 = lean_ctor_get(x_4, 16);
x_23 = lean_ctor_get(x_4, 17);
x_24 = lean_ctor_get(x_4, 18);
x_25 = lean_ctor_get(x_4, 19);
x_26 = lean_ctor_get(x_4, 20);
x_27 = lean_ctor_get(x_4, 21);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*23 + 1);
x_29 = lean_ctor_get(x_4, 22);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
x_30 = x_4;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0(x_1, x_2, x_25, x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 19, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_8);
lean_ctor_set(x_35, 4, x_9);
lean_ctor_set(x_35, 5, x_10);
lean_ctor_set(x_35, 6, x_11);
lean_ctor_set(x_35, 7, x_12);
lean_ctor_set(x_35, 8, x_13);
lean_ctor_set(x_35, 9, x_14);
lean_ctor_set(x_35, 10, x_15);
lean_ctor_set(x_35, 11, x_16);
lean_ctor_set(x_35, 12, x_17);
lean_ctor_set(x_35, 13, x_18);
lean_ctor_set(x_35, 14, x_19);
lean_ctor_set(x_35, 15, x_21);
lean_ctor_set(x_35, 16, x_22);
lean_ctor_set(x_35, 17, x_23);
lean_ctor_set(x_35, 18, x_24);
lean_ctor_set(x_35, 19, x_32);
lean_ctor_set(x_35, 20, x_26);
lean_ctor_set(x_35, 21, x_27);
lean_ctor_set(x_35, 22, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_40; 
x_9 = lean_ctor_get(x_8, 0);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
x_10 = x_8;
x_11 = x_40;
goto block_39;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 25);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_del_object(x_10);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo_default;
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_22 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_21, x_20, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_23 = x_22;
x_24 = x_29;
goto block_28;
}
else
{
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_18);
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_18);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_18);
x_31 = lean_ctor_get(x_22, 0);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
x_32 = x_22;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_dec(x_1);
return x_17;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_8, 0);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
x_42 = x_8;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_39; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_ctor_get(x_5, 8);
x_15 = lean_ctor_get(x_5, 9);
x_16 = lean_ctor_get(x_5, 10);
x_17 = lean_ctor_get(x_5, 11);
x_18 = lean_ctor_get(x_5, 12);
x_19 = lean_ctor_get(x_5, 13);
x_20 = lean_ctor_get(x_5, 14);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*23);
x_22 = lean_ctor_get(x_5, 15);
x_23 = lean_ctor_get(x_5, 16);
x_24 = lean_ctor_get(x_5, 17);
x_25 = lean_ctor_get(x_5, 18);
x_26 = lean_ctor_get(x_5, 19);
x_27 = lean_ctor_get(x_5, 20);
x_28 = lean_ctor_get(x_5, 21);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*23 + 1);
x_30 = lean_ctor_get(x_5, 22);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
x_31 = x_5;
x_32 = x_39;
goto block_38;
}
else
{
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_33, 2, x_3);
x_34 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1___redArg(x_27, x_4, x_33);
if (x_32 == 0)
{
lean_ctor_set(x_31, 20, x_34);
x_35 = x_31;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_7);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_9);
lean_ctor_set(x_37, 4, x_10);
lean_ctor_set(x_37, 5, x_11);
lean_ctor_set(x_37, 6, x_12);
lean_ctor_set(x_37, 7, x_13);
lean_ctor_set(x_37, 8, x_14);
lean_ctor_set(x_37, 9, x_15);
lean_ctor_set(x_37, 10, x_16);
lean_ctor_set(x_37, 11, x_17);
lean_ctor_set(x_37, 12, x_18);
lean_ctor_set(x_37, 13, x_19);
lean_ctor_set(x_37, 14, x_20);
lean_ctor_set(x_37, 15, x_22);
lean_ctor_set(x_37, 16, x_23);
lean_ctor_set(x_37, 17, x_24);
lean_ctor_set(x_37, 18, x_25);
lean_ctor_set(x_37, 19, x_26);
lean_ctor_set(x_37, 20, x_34);
lean_ctor_set(x_37, 21, x_28);
lean_ctor_set(x_37, 22, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*23, x_21);
lean_ctor_set_uint8(x_37, sizeof(void*)*23 + 1, x_29);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_82; 
x_15 = lean_ctor_get(x_14, 0);
x_82 = !lean_is_exclusive(x_14);
if (x_82 == 0)
{
x_16 = x_14;
x_17 = x_82;
goto block_81;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 20);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(x_18, x_1);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
lean_object* x_27; 
lean_dec(x_19);
lean_del_object(x_16);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_2, x_3, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_2, x_3, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_32);
lean_dec(x_30);
lean_inc_ref(x_1);
x_33 = l_Lean_Expr_app___override(x_31, x_1);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl;
lean_inc_ref(x_33);
x_35 = l_Lean_Expr_app___override(x_34, x_33);
lean_inc_ref(x_1);
lean_inc_ref(x_35);
lean_inc_ref(x_33);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar___lam__0), 5, 4);
lean_closure_set(x_36, 0, x_33);
lean_closure_set(x_36, 1, x_32);
lean_closure_set(x_36, 2, x_35);
lean_closure_set(x_36, 3, x_1);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_38 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_37, x_36, x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(x_37, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_47; 
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_39, 0);
lean_dec(x_48);
x_40 = x_39;
x_41 = x_47;
goto block_46;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_35);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_43 = x_40;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec_ref(x_35);
lean_dec_ref(x_33);
x_49 = lean_ctor_get(x_39, 0);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
x_50 = x_39;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_35);
lean_dec_ref(x_33);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_38, 0);
x_64 = !lean_is_exclusive(x_38);
if (x_64 == 0)
{
x_58 = x_38;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_38);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_29, 0);
x_72 = !lean_is_exclusive(x_29);
if (x_72 == 0)
{
x_66 = x_29;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_29);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_27, 0);
x_80 = !lean_is_exclusive(x_27);
if (x_80 == 0)
{
x_74 = x_27;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_27);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_14, 0);
x_90 = !lean_is_exclusive(x_14);
if (x_90 == 0)
{
x_84 = x_14;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_14);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_28; 
x_6 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_7 = x_5;
x_8 = x_28;
goto block_27;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 20);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__0___redArg(x_9, x_1);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
x_12 = x_10;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_15);
x_16 = x_7;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
x_23 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_23);
x_24 = x_7;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_5, 0);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
x_30 = x_5;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntTermType_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_spec__1_spec__2___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_16; 
x_6 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_7 = x_5;
x_8 = x_16;
goto block_15;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 20);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg(x_9, x_1);
x_11 = lean_box(x_10);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_12 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
x_18 = x_5;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isToIntTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_isToIntTerm_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__7));
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_6 = lean_ctor_get(x_5, 0);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
x_7 = x_5;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_9);
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_box(x_14);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_15);
x_16 = x_7;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(x_13);
lean_dec(x_13);
x_20 = lean_box(x_19);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_20);
x_21 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
x_24 = 0;
x_25 = lean_box(x_24);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_25);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
x_29 = 0;
x_30 = lean_box(x_29);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_30);
x_31 = x_7;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_36 = lean_ctor_get(x_5, 0);
x_43 = !lean_is_exclusive(x_5);
if (x_43 == 0)
{
x_37 = x_5;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_reportMissingToIntAdapter_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_4, x_5, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_230; 
x_17 = lean_ctor_get(x_16, 0);
x_230 = !lean_is_exclusive(x_16);
if (x_230 == 0)
{
x_18 = x_16;
x_19 = x_230;
goto block_229;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 5);
lean_inc(x_20);
lean_dec(x_17);
switch (lean_obj_tag(x_20)) {
case 3:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
case 0:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_del_object(x_18);
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(x_20, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(x_4, x_5, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_100; 
x_31 = lean_ctor_get(x_30, 0);
x_100 = !lean_is_exclusive(x_30);
if (x_100 == 0)
{
x_32 = x_30;
x_33 = x_100;
goto block_99;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_100;
goto block_99;
}
block_99:
{
uint8_t x_34; 
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_del_object(x_32);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = lean_grind_preprocess(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_36);
x_37 = l_Lean_Meta_Simp_Result_getProof(x_36, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_39 = l_Lean_Meta_mkEqTrans(x_3, x_38, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_43);
lean_dec(x_36);
x_44 = lean_box(0);
lean_inc_ref(x_43);
x_45 = lean_grind_internalize(x_43, x_42, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_53; 
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_45, 0);
lean_dec(x_54);
x_46 = x_45;
x_47 = x_53;
goto block_52;
}
else
{
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_40);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_48);
x_49 = x_46;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_43);
lean_dec(x_40);
x_55 = lean_ctor_get(x_45, 0);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
x_56 = x_45;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = lean_ctor_get(x_41, 0);
x_70 = !lean_is_exclusive(x_41);
if (x_70 == 0)
{
x_64 = x_41;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_41);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_36);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_39, 0);
x_78 = !lean_is_exclusive(x_39);
if (x_78 == 0)
{
x_72 = x_39;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_39);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_36);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_37, 0);
x_86 = !lean_is_exclusive(x_37);
if (x_86 == 0)
{
x_80 = x_37;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_37);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_35, 0);
x_94 = !lean_is_exclusive(x_35);
if (x_94 == 0)
{
x_88 = x_35;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_35);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_29);
lean_ctor_set(x_95, 1, x_3);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_95);
x_96 = x_32;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_101 = lean_ctor_get(x_30, 0);
x_108 = !lean_is_exclusive(x_30);
if (x_108 == 0)
{
x_102 = x_30;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_30);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_109 = lean_ctor_get(x_28, 0);
x_116 = !lean_is_exclusive(x_28);
if (x_116 == 0)
{
x_110 = x_28;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_28);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
else
{
lean_object* x_117; 
lean_dec_ref(x_20);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_4, x_5, x_13);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_4, x_5, x_13);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_210; 
x_120 = lean_ctor_get(x_119, 0);
x_210 = !lean_is_exclusive(x_119);
if (x_210 == 0)
{
x_121 = x_119;
x_122 = x_210;
goto block_209;
}
else
{
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_box(0);
x_122 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_26, 0);
x_124 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_124);
lean_dec(x_118);
x_125 = lean_ctor_get(x_120, 8);
lean_inc(x_125);
lean_dec(x_120);
lean_inc_ref(x_123);
lean_inc_ref(x_2);
x_126 = l_Lean_mkIntMod(x_2, x_123);
x_127 = l_Lean_Expr_app___override(x_124, x_1);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3);
x_207 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__0(x_206);
x_128 = x_207;
goto block_205;
}
else
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_125, 0);
lean_inc(x_208);
lean_dec_ref(x_125);
x_128 = x_208;
goto block_205;
}
block_205:
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; uint8_t x_202; 
lean_inc_ref(x_2);
x_129 = l_Lean_mkApp3(x_128, x_127, x_2, x_3);
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isNumeral(x_26);
x_202 = !lean_is_exclusive(x_26);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_26, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_26, 0);
lean_dec(x_204);
x_131 = x_26;
x_132 = x_202;
goto block_201;
}
else
{
lean_dec(x_26);
x_131 = lean_box(0);
x_132 = x_202;
goto block_201;
}
block_201:
{
if (x_130 == 0)
{
lean_object* x_133; 
lean_del_object(x_121);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_133 = lean_grind_preprocess(x_126, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_134);
x_135 = l_Lean_Meta_Simp_Result_getProof(x_134, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_137 = l_Lean_Meta_mkEqTrans(x_129, x_136, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_141);
lean_dec(x_134);
x_142 = lean_box(0);
lean_inc_ref(x_141);
x_143 = lean_grind_internalize(x_141, x_140, x_142, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; uint8_t x_153; 
x_153 = !lean_is_exclusive(x_143);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_143, 0);
lean_dec(x_154);
x_144 = x_143;
x_145 = x_153;
goto block_152;
}
else
{
lean_dec(x_143);
x_144 = lean_box(0);
x_145 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_146; 
if (x_132 == 0)
{
lean_ctor_set(x_131, 1, x_138);
lean_ctor_set(x_131, 0, x_141);
x_146 = x_131;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_138);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_146);
x_147 = x_144;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_146);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec_ref(x_141);
lean_dec(x_138);
lean_del_object(x_131);
x_155 = lean_ctor_get(x_143, 0);
x_162 = !lean_is_exclusive(x_143);
if (x_162 == 0)
{
x_156 = x_143;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_143);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_138);
lean_dec(x_134);
lean_del_object(x_131);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_163 = lean_ctor_get(x_139, 0);
x_170 = !lean_is_exclusive(x_139);
if (x_170 == 0)
{
x_164 = x_139;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_139);
x_164 = lean_box(0);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_165 == 0)
{
x_166 = x_164;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_163);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_178; 
lean_dec(x_134);
lean_del_object(x_131);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_171 = lean_ctor_get(x_137, 0);
x_178 = !lean_is_exclusive(x_137);
if (x_178 == 0)
{
x_172 = x_137;
x_173 = x_178;
goto block_177;
}
else
{
lean_inc(x_171);
lean_dec(x_137);
x_172 = lean_box(0);
x_173 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_174; 
if (x_173 == 0)
{
x_174 = x_172;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_186; 
lean_dec(x_134);
lean_del_object(x_131);
lean_dec_ref(x_129);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_179 = lean_ctor_get(x_135, 0);
x_186 = !lean_is_exclusive(x_135);
if (x_186 == 0)
{
x_180 = x_135;
x_181 = x_186;
goto block_185;
}
else
{
lean_inc(x_179);
lean_dec(x_135);
x_180 = lean_box(0);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; 
if (x_181 == 0)
{
x_182 = x_180;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_179);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_194; 
lean_del_object(x_131);
lean_dec_ref(x_129);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_187 = lean_ctor_get(x_133, 0);
x_194 = !lean_is_exclusive(x_133);
if (x_194 == 0)
{
x_188 = x_133;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_dec(x_133);
x_188 = lean_box(0);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_189 == 0)
{
x_190 = x_188;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_187);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
if (x_132 == 0)
{
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 0, x_126);
x_195 = x_131;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_126);
lean_ctor_set(x_200, 1, x_129);
x_195 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_196; 
if (x_122 == 0)
{
lean_ctor_set(x_121, 0, x_195);
x_196 = x_121;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_195);
x_196 = x_198;
goto block_197;
}
block_197:
{
return x_196;
}
}
}
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_218; 
lean_dec(x_118);
lean_dec_ref(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_211 = lean_ctor_get(x_119, 0);
x_218 = !lean_is_exclusive(x_119);
if (x_218 == 0)
{
x_212 = x_119;
x_213 = x_218;
goto block_217;
}
else
{
lean_inc(x_211);
lean_dec(x_119);
x_212 = lean_box(0);
x_213 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_214; 
if (x_213 == 0)
{
x_214 = x_212;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_211);
x_214 = x_216;
goto block_215;
}
block_215:
{
return x_214;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_226; 
lean_dec_ref(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_219 = lean_ctor_get(x_117, 0);
x_226 = !lean_is_exclusive(x_117);
if (x_226 == 0)
{
x_220 = x_117;
x_221 = x_226;
goto block_225;
}
else
{
lean_inc(x_219);
lean_dec(x_117);
x_220 = lean_box(0);
x_221 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_222; 
if (x_221 == 0)
{
x_222 = x_220;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_219);
x_222 = x_224;
goto block_223;
}
block_223:
{
return x_222;
}
}
}
}
}
default: 
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_20);
lean_del_object(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_227 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__5);
x_228 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg(x_227, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_228;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_238; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_231 = lean_ctor_get(x_16, 0);
x_238 = !lean_is_exclusive(x_16);
if (x_238 == 0)
{
x_232 = x_16;
x_233 = x_238;
goto block_237;
}
else
{
lean_inc(x_231);
lean_dec(x_16);
x_232 = lean_box(0);
x_233 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_234; 
if (x_233 == 0)
{
x_234 = x_232;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_231);
x_234 = x_236;
goto block_235;
}
block_235:
{
return x_234;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_7 = lean_ctor_get(x_6, 0);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
x_8 = x_6;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_10);
lean_dec(x_7);
x_11 = l_Lean_Expr_app___override(x_10, x_1);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_6, 0);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
x_18 = x_6;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_1, x_2, x_3, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 3);
lean_inc(x_73);
lean_dec_ref(x_1);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap___closed__3);
x_86 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap_spec__0(x_85);
x_74 = x_86;
goto block_84;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_70, 0);
lean_inc(x_87);
lean_dec_ref(x_70);
x_74 = x_87;
goto block_84;
}
block_69:
{
lean_object* x_35; 
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc_ref(x_3);
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(x_3, x_22, x_7, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc_ref(x_33);
lean_inc(x_25);
lean_inc_ref(x_4);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(x_4, x_23, x_8, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_68; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_ctor_get(x_40, 1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
x_43 = x_40;
x_44 = x_68;
goto block_67;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_40);
x_43 = lean_box(0);
x_44 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_41);
lean_inc(x_37);
x_45 = l_Lean_mkApp6(x_21, x_3, x_4, x_37, x_41, x_38, x_42);
x_46 = lean_apply_2(x_2, x_37, x_41);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_46, x_24, x_25, x_33);
lean_dec_ref(x_33);
lean_dec(x_25);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_58; 
x_48 = lean_ctor_get(x_47, 0);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
x_49 = x_47;
x_50 = x_58;
goto block_57;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_51; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_45);
lean_ctor_set(x_43, 0, x_48);
x_51 = x_43;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_45);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec_ref(x_45);
lean_del_object(x_43);
x_59 = lean_ctor_get(x_47, 0);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
x_60 = x_47;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_25);
lean_dec_ref(x_21);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_39;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_35;
}
}
block_84:
{
lean_object* x_75; 
lean_inc_ref(x_5);
x_75 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(x_5);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_71);
lean_inc_ref(x_6);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_73);
x_21 = x_74;
x_22 = x_5;
x_23 = x_6;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
else
{
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_74);
lean_dec_ref(x_6);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec_ref(x_73);
x_21 = x_78;
x_22 = x_5;
x_23 = x_77;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
else
{
lean_dec_ref(x_76);
lean_dec(x_73);
x_21 = x_74;
x_22 = x_5;
x_23 = x_6;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec_ref(x_75);
lean_inc_ref(x_6);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_dec(x_71);
if (lean_obj_tag(x_72) == 1)
{
lean_object* x_81; 
lean_dec_ref(x_74);
lean_dec_ref(x_5);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec_ref(x_72);
x_21 = x_81;
x_22 = x_79;
x_23 = x_6;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
else
{
lean_dec(x_79);
lean_dec(x_72);
x_21 = x_74;
x_22 = x_5;
x_23 = x_6;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
}
else
{
lean_dec(x_72);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_74);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = lean_ctor_get(x_71, 0);
lean_inc(x_83);
lean_dec_ref(x_71);
x_21 = x_83;
x_22 = x_79;
x_23 = x_82;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
else
{
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec(x_71);
x_21 = x_74;
x_22 = x_5;
x_23 = x_6;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
goto block_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_cleanupAnnotations(x_1);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_6);
goto block_5;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_dec_ref(x_8);
goto block_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
goto block_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___closed__2));
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec_ref(x_14);
if (x_16 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_10);
goto block_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_getOfNatThm_x3f___redArg(x_3, x_4, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_hasNumericLoHi___redArg(x_3, x_4, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_2);
x_20 = l_Lean_mkNatLit(x_2);
x_21 = l_Lean_Expr_app___override(x_17, x_20);
x_22 = lean_unbox(x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_to_int(x_2);
x_24 = l_Lean_mkIntLit(x_23);
lean_dec(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(x_1, x_24, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_3, x_4, x_12);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 5);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_nat_to_int(x_2);
x_30 = l_Lean_mkIntLit(x_29);
lean_dec(x_29);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_wrap(x_28, x_30, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_33 = x_31;
x_34 = x_40;
goto block_39;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_21);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_21);
x_41 = lean_ctor_get(x_31, 0);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_42 = x_31;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec_ref(x_21);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_2);
x_49 = lean_ctor_get(x_26, 0);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
x_50 = x_26;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_26);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_18, 0);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
x_58 = x_18;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_18);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_16);
lean_dec(x_2);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_15, 0);
x_73 = !lean_is_exclusive(x_15);
if (x_73 == 0)
{
x_67 = x_15;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_15);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_getPowThm_x3f___redArg(x_4, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_48; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
x_23 = x_20;
x_24 = x_48;
goto block_47;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_3);
lean_inc(x_21);
x_25 = l_Lean_mkIntPowNat(x_21, x_3);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_25, x_4, x_5, x_13);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_38; 
x_27 = lean_ctor_get(x_26, 0);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
x_28 = x_26;
x_29 = x_38;
goto block_37;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_mkApp4(x_18, x_2, x_3, x_21, x_22);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_30);
lean_ctor_set(x_23, 0, x_27);
x_31 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_30);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_31);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_26, 0);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
x_40 = x_26;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_19;
}
}
else
{
lean_object* x_49; 
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_16, 0);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
x_51 = x_16;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_4);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_ToIntThms_mkResult(x_2, x_3, x_4, x_5, x_22, x_26, x_23, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_28;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (x_2 == 0)
{
lean_object* x_54; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_5);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_getModThm_x3f___redArg(x_5, x_6, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_27 = x_55;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_13;
x_37 = x_14;
x_38 = x_15;
goto block_53;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_54, 0);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
x_57 = x_54;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_5);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_getDivThm_x3f___redArg(x_5, x_6, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_27 = x_65;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_13;
x_37 = x_14;
x_38 = x_15;
goto block_53;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_64, 0);
x_73 = !lean_is_exclusive(x_64);
if (x_73 == 0)
{
x_67 = x_64;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_mkApp6(x_19, x_3, x_4, x_21, x_20, x_17, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
block_53:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec_ref(x_27);
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc_ref(x_3);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_3, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc_ref(x_4);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_4, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
if (x_2 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
lean_inc(x_42);
x_48 = l_Lean_mkIntMod(x_42, x_46);
x_17 = x_43;
x_18 = x_47;
x_19 = x_39;
x_20 = x_46;
x_21 = x_42;
x_22 = x_48;
goto block_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
lean_inc(x_49);
lean_inc(x_42);
x_51 = l_Lean_mkIntDiv(x_42, x_49);
x_17 = x_43;
x_18 = x_50;
x_19 = x_39;
x_20 = x_49;
x_21 = x_42;
x_22 = x_51;
goto block_26;
}
}
else
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_44;
}
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_40;
}
}
else
{
lean_object* x_52; 
lean_dec(x_27);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
lean_dec(x_28);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_getSubThm_x3f___redArg(x_4, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc_ref(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_52; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_27 = x_24;
x_28 = x_52;
goto block_51;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_29; lean_object* x_30; 
lean_inc(x_25);
lean_inc(x_21);
x_29 = l_Lean_mkIntSub(x_21, x_25);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_29, x_4, x_5, x_13);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_42; 
x_31 = lean_ctor_get(x_30, 0);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
x_32 = x_30;
x_33 = x_42;
goto block_41;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_mkApp6(x_18, x_2, x_3, x_21, x_25, x_22, x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_31);
x_35 = x_27;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_34);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_del_object(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_30, 0);
x_50 = !lean_is_exclusive(x_30);
if (x_50 == 0)
{
x_44 = x_30;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_23;
}
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_19;
}
}
else
{
lean_object* x_53; 
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_16, 0);
x_61 = !lean_is_exclusive(x_16);
if (x_61 == 0)
{
x_55 = x_16;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_getNegThm_x3f___redArg(x_3, x_4, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc_ref(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_47; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
x_22 = x_19;
x_23 = x_47;
goto block_46;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_20);
x_24 = l_Lean_mkIntNeg(x_20);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkWrap___redArg(x_24, x_3, x_4, x_12);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_37; 
x_26 = lean_ctor_get(x_25, 0);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
x_27 = x_25;
x_28 = x_37;
goto block_36;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_mkApp3(x_17, x_2, x_20, x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_29);
lean_ctor_set(x_22, 0, x_26);
x_30 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_29);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_25, 0);
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
x_39 = x_25;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
else
{
lean_object* x_48; 
lean_dec(x_16);
lean_dec_ref(x_2);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_15, 0);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
x_50 = x_15;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__28));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_isZero___closed__0);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Expr_cleanupAnnotations(x_15);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_20);
lean_dec_ref(x_19);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_23);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__2));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__4));
x_32 = l_Lean_Expr_isConstOf(x_28, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Expr_isApp(x_28);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_36 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__5));
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__7));
x_39 = l_Lean_Expr_isConstOf(x_35, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isApp(x_35);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_35);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_42);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_46);
x_47 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_42);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_50);
x_51 = l_Lean_Expr_appFnCleanup___redArg(x_47);
x_52 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__9));
x_53 = l_Lean_Expr_isConstOf(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__12));
x_55 = l_Lean_Expr_isConstOf(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__15));
x_57 = l_Lean_Expr_isConstOf(x_51, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__18));
x_59 = l_Lean_Expr_isConstOf(x_51, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__21));
x_61 = l_Lean_Expr_isConstOf(x_51, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__24));
x_63 = l_Lean_Expr_isConstOf(x_51, x_62);
lean_dec_ref(x_51);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec_ref(x_50);
lean_dec_ref(x_46);
lean_dec_ref(x_42);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_50, x_46, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_46);
lean_dec_ref(x_50);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_66;
}
else
{
lean_object* x_67; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_2);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_getAddThms___redArg(x_2, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__25));
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin(x_1, x_68, x_69, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_67, 0);
x_78 = !lean_is_exclusive(x_67);
if (x_78 == 0)
{
x_72 = x_67;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_51);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_50, x_46, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_46);
lean_dec_ref(x_50);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_80;
}
else
{
lean_object* x_81; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_2);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_getMulThms___redArg(x_2, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__26));
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin(x_1, x_82, x_83, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_81, 0);
x_92 = !lean_is_exclusive(x_81);
if (x_92 == 0)
{
x_86 = x_81;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec_ref(x_51);
x_93 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_50, x_46, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_46);
lean_dec_ref(x_50);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_94 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod(x_1, x_93, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec_ref(x_51);
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_50, x_46, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_46);
lean_dec_ref(x_50);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_97;
}
else
{
lean_object* x_98; 
x_98 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod(x_1, x_55, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_51);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isHomo(x_50, x_46, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_46);
lean_dec_ref(x_50);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_100;
}
else
{
lean_object* x_101; 
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub(x_1, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec_ref(x_51);
x_102 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_50, x_42);
lean_dec_ref(x_42);
lean_dec_ref(x_50);
if (x_102 == 0)
{
lean_dec_ref(x_46);
x_24 = x_102;
goto block_27;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_mkOfNatThm_x3f___redArg___closed__3));
x_104 = l_Lean_Expr_isConstOf(x_46, x_103);
lean_dec_ref(x_46);
x_24 = x_104;
goto block_27;
}
}
}
}
}
}
else
{
lean_object* x_105; 
lean_dec_ref(x_35);
lean_dec_ref(x_23);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec_ref(x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_106 = l_Lean_Meta_getNatValue_x3f(x_23, x_9, x_10, x_11, x_12);
lean_dec_ref(x_23);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_19);
x_111 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(x_1, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_111;
}
else
{
lean_object* x_112; 
x_112 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isFinInstOfNat_x3f___redArg(x_19);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_134; 
x_113 = lean_ctor_get(x_112, 0);
x_134 = !lean_is_exclusive(x_112);
if (x_134 == 0)
{
x_114 = x_112;
x_115 = x_134;
goto block_133;
}
else
{
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_box(0);
x_115 = x_134;
goto block_133;
}
block_133:
{
if (lean_obj_tag(x_113) == 1)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_131; 
lean_dec(x_108);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
lean_dec_ref(x_113);
x_117 = lean_ctor_get(x_116, 0);
x_118 = lean_ctor_get(x_116, 1);
x_131 = !lean_is_exclusive(x_116);
if (x_131 == 0)
{
x_119 = x_116;
x_120 = x_131;
goto block_130;
}
else
{
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_116);
x_119 = lean_box(0);
x_120 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__29);
x_122 = l_Lean_mkAppB(x_121, x_117, x_118);
x_123 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30);
if (x_120 == 0)
{
lean_ctor_set(x_119, 1, x_122);
lean_ctor_set(x_119, 0, x_123);
x_124 = x_119;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_122);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_115 == 0)
{
lean_ctor_set(x_114, 0, x_124);
x_125 = x_114;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_124);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
else
{
lean_object* x_132; 
lean_del_object(x_114);
lean_dec(x_113);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(x_1, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_132;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
lean_dec(x_108);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_112, 0);
x_142 = !lean_is_exclusive(x_112);
if (x_142 == 0)
{
x_136 = x_112;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_dec(x_112);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_107);
lean_dec_ref(x_19);
x_143 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_151; 
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_144 = lean_ctor_get(x_106, 0);
x_151 = !lean_is_exclusive(x_106);
if (x_151 == 0)
{
x_145 = x_106;
x_146 = x_151;
goto block_150;
}
else
{
lean_inc(x_144);
lean_dec(x_106);
x_145 = lean_box(0);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_146 == 0)
{
x_147 = x_145;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_144);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
}
else
{
lean_object* x_152; 
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_2);
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_getZeroThm_x3f___redArg(x_2, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_164; 
x_153 = lean_ctor_get(x_152, 0);
x_164 = !lean_is_exclusive(x_152);
if (x_164 == 0)
{
x_154 = x_152;
x_155 = x_164;
goto block_163;
}
else
{
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = x_164;
goto block_163;
}
block_163:
{
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec_ref(x_153);
x_157 = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___closed__30);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
if (x_155 == 0)
{
lean_ctor_set(x_154, 0, x_158);
x_159 = x_154;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_158);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
else
{
lean_object* x_162; 
lean_del_object(x_154);
lean_dec(x_153);
x_162 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_162;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_152, 0);
x_172 = !lean_is_exclusive(x_152);
if (x_172 == 0)
{
x_166 = x_152;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_152);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
}
else
{
lean_object* x_173; 
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_173 = l_Lean_Meta_getNatValue_x3f(x_19, x_9, x_10, x_11, x_12);
lean_dec_ref(x_19);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
if (lean_obj_tag(x_174) == 1)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntOfNat(x_1, x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_176;
}
else
{
lean_object* x_177; 
lean_dec(x_174);
x_177 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_173, 0);
x_185 = !lean_is_exclusive(x_173);
if (x_185 == 0)
{
x_179 = x_173;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_173);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
block_27:
{
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_23);
lean_dec_ref(x_19);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_mkToIntVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow(x_1, x_23, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_193; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_186 = lean_ctor_get(x_14, 0);
x_193 = !lean_is_exclusive(x_14);
if (x_193 == 0)
{
x_187 = x_14;
x_188 = x_193;
goto block_192;
}
else
{
lean_inc(x_186);
lean_dec(x_14);
x_187 = lean_box(0);
x_188 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_189; 
if (x_188 == 0)
{
x_189 = x_187;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_186);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandIfWrap(x_1, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_18;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntAndExpandWrap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_toIntBin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processNeg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processPow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processSub(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27_processDivMod(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_67; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_toInt_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_isWrap(x_69);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_expandWrap(x_1, x_72, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_14 = x_75;
x_15 = x_76;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
goto block_66;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_73;
}
}
else
{
lean_dec(x_71);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = x_69;
x_15 = x_70;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
goto block_66;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_67;
}
block_66:
{
lean_object* x_26; 
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_26 = lean_grind_preprocess(x_14, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_57; 
x_27 = lean_ctor_get(x_26, 0);
x_57 = !lean_is_exclusive(x_26);
if (x_57 == 0)
{
x_28 = x_26;
x_29 = x_57;
goto block_56;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 1);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_30);
lean_del_object(x_28);
x_31 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_mkEqTrans(x_15, x_32, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
x_34 = lean_ctor_get(x_33, 0);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
x_35 = x_33;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_31);
x_43 = lean_ctor_get(x_33, 0);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
x_44 = x_33;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_51 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_51);
lean_dec(x_27);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_15);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_52);
x_53 = x_28;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_15);
x_58 = lean_ctor_get(x_26, 0);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
x_59 = x_26;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_26);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_toInt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_toInt___boxed), 13, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run_x3f___redArg(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Nat_mkType;
x_41 = lean_expr_eqv(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Int_mkType;
x_43 = lean_expr_eqv(x_1, x_42);
x_13 = x_43;
goto block_39;
}
else
{
x_13 = x_41;
goto block_39;
}
block_39:
{
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_16 = x_14;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_15);
x_22 = 1;
x_23 = lean_box(x_22);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(x_13);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___closed__0);
x_15 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_12(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__2));
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(518u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__2));
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(510u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_getInfo___redArg(x_3, x_4, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_115; 
x_16 = lean_ctor_get(x_15, 0);
x_115 = !lean_is_exclusive(x_15);
if (x_115 == 0)
{
x_17 = x_15;
x_18 = x_115;
goto block_114;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_77; 
x_19 = lean_ctor_get(x_16, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 12);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_19);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_lo_x3f(x_19);
if (lean_obj_tag(x_77) == 1)
{
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_110; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 1);
x_110 = !lean_is_exclusive(x_78);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_78, 0);
lean_dec(x_111);
x_80 = x_78;
x_81 = x_110;
goto block_109;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_110;
goto block_109;
}
block_109:
{
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_104; 
x_82 = lean_ctor_get(x_20, 0);
x_104 = !lean_is_exclusive(x_20);
if (x_104 == 0)
{
x_83 = x_20;
x_84 = x_104;
goto block_103;
}
else
{
lean_inc(x_82);
lean_dec(x_20);
x_83 = lean_box(0);
x_84 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_102; 
x_85 = lean_ctor_get(x_79, 0);
x_102 = !lean_is_exclusive(x_79);
if (x_102 == 0)
{
x_86 = x_79;
x_87 = x_102;
goto block_101;
}
else
{
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_box(0);
x_87 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__4);
if (x_87 == 0)
{
lean_ctor_set_tag(x_86, 0);
x_89 = x_86;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_85);
x_89 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_inc(x_1);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_1);
lean_ctor_set(x_90, 2, x_89);
lean_inc_ref(x_2);
x_91 = l_Lean_Expr_app___override(x_82, x_2);
if (x_84 == 0)
{
lean_ctor_set_tag(x_83, 4);
lean_ctor_set(x_83, 0, x_91);
x_92 = x_83;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_98, 0, x_91);
x_92 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_93; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 1, x_92);
lean_ctor_set(x_80, 0, x_90);
x_93 = x_80;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_92);
x_93 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_94; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_94 = lean_grind_cutsat_assert_le(x_93, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_12;
x_32 = x_13;
goto block_76;
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_del_object(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_94;
}
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_del_object(x_80);
lean_dec(x_79);
x_105 = lean_ctor_get(x_20, 0);
lean_inc(x_105);
lean_dec_ref(x_20);
lean_inc_ref(x_2);
x_106 = l_Lean_Expr_app___override(x_105, x_2);
x_107 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Meta_Grind_pushNewFact(x_106, x_107, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_108);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_12;
x_32 = x_13;
goto block_76;
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_del_object(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_108;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_77);
lean_dec(x_20);
x_112 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_113);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_12;
x_32 = x_13;
goto block_76;
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_del_object(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_113;
}
}
}
else
{
lean_dec(x_77);
lean_dec(x_20);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_12;
x_32 = x_13;
goto block_76;
}
block_76:
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_SymbolicIntInterval_hi_x3f(x_19);
if (lean_obj_tag(x_33) == 1)
{
lean_del_object(x_17);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_68; 
lean_dec(x_22);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 1);
x_68 = !lean_is_exclusive(x_34);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_34, 0);
lean_dec(x_69);
x_36 = x_34;
x_37 = x_68;
goto block_67;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_68;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_62; 
x_38 = lean_ctor_get(x_21, 0);
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
x_39 = x_21;
x_40 = x_62;
goto block_61;
}
else
{
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_box(0);
x_40 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_60; 
x_41 = lean_ctor_get(x_35, 0);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
x_42 = x_35;
x_43 = x_60;
goto block_59;
}
else
{
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_SymbolicBound_mkIntNegSucc___redArg___closed__0);
x_45 = lean_int_neg(x_41);
lean_dec(x_41);
x_46 = lean_int_add(x_45, x_44);
lean_dec(x_45);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_46);
x_47 = x_42;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_46);
x_47 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_Expr_app___override(x_38, x_2);
if (x_40 == 0)
{
lean_ctor_set_tag(x_39, 4);
lean_ctor_set(x_39, 0, x_49);
x_50 = x_39;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_49);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_50);
lean_ctor_set(x_36, 0, x_48);
x_51 = x_36;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_50);
x_51 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_52; 
x_52 = lean_grind_cutsat_assert_le(x_51, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_del_object(x_36);
lean_dec(x_35);
lean_dec(x_1);
x_63 = lean_ctor_get(x_21, 0);
lean_inc(x_63);
lean_dec_ref(x_21);
x_64 = l_Lean_Expr_app___override(x_63, x_2);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Meta_Grind_pushNewFact(x_64, x_65, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_66;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_33);
lean_dec(x_21);
lean_dec_ref(x_2);
lean_dec(x_1);
x_70 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___closed__3);
x_71 = l_panic___at___00Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds_spec__0(x_70, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_72);
x_73 = x_17;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_15, 0);
x_123 = !lean_is_exclusive(x_15);
if (x_123 == 0)
{
x_117 = x_15;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_15);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f_go_x3f___lam__1___closed__5));
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___lam__0___boxed), 14, 2);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_19);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(x_26, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_31;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToIntLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToIntLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt_0__Lean_Meta_Grind_Arith_Cutsat_intRfl);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_ToIntLemmas(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToIntLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
}
#ifdef __cplusplus
}
#endif

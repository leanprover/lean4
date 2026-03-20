// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Simp.Main public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.MatchDiscrOnly import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons import Lean.Meta.Sym.Util
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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_dsimpMainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_abstractNestedProofs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind simp"};
static const lean_object* l_Lean_Meta_Grind_simpCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_dsimpCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind dsimp"};
static const lean_object* l_Lean_Meta_Grind_dsimpCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_dsimpCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_preprocessImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 174, 175, 152, 201, 92, 177, 229)}};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_preprocessImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__4;
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pushNewFact"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 237, 7, 223, 90, 130, 102, 106)}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " ==> "};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNewFact_x27___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNewFact_x27___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(lean_object* v_category_1_, lean_object* v_opts_2_, lean_object* v_act_3_, lean_object* v_decl_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_apply_9(v_act_3_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
v___x_16_ = l_Lean_profileitIOUnsafe___redArg(v_category_1_, v_opts_2_, v___x_15_, v_decl_4_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg___boxed(lean_object* v_category_17_, lean_object* v_opts_18_, lean_object* v_act_19_, lean_object* v_decl_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v_category_17_, v_opts_18_, v_act_19_, v_decl_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec_ref(v_opts_18_);
lean_dec_ref(v_category_17_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0(lean_object* v_00_u03b1_32_, lean_object* v_category_33_, lean_object* v_opts_34_, lean_object* v_act_35_, lean_object* v_decl_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v_category_33_, v_opts_34_, v_act_35_, v_decl_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___boxed(lean_object* v_00_u03b1_48_, lean_object* v_category_49_, lean_object* v_opts_50_, lean_object* v_act_51_, lean_object* v_decl_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0(v_00_u03b1_48_, v_category_49_, v_opts_50_, v_act_51_, v_decl_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec_ref(v_opts_50_);
lean_dec_ref(v_category_49_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = lean_unsigned_to_nat(16u);
v___x_66_ = lean_mk_array(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__0, &l_Lean_Meta_Grind_simpCore___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__2, &l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__3, &l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3);
v___x_74_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__1, &l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1);
v___x_75_ = 1;
v___x_76_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_73_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*2, v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__3, &l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(32u);
v___x_81_ = lean_mk_empty_array_with_capacity(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7(void){
_start:
{
size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_unsigned_to_nat(32u);
v___x_86_ = lean_mk_empty_array_with_capacity(v___x_85_);
v___x_87_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__6, &l_Lean_Meta_Grind_simpCore___lam__0___closed__6_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6);
v___x_88_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_84_);
lean_ctor_set(v___x_88_, 3, v___x_84_);
lean_ctor_set_usize(v___x_88_, 4, v___x_83_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__7, &l_Lean_Meta_Grind_simpCore___lam__0___closed__7_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7);
v___x_90_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__3, &l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3);
v___x_91_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set(v___x_91_, 3, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__8, &l_Lean_Meta_Grind_simpCore___lam__0___closed__8_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__5, &l_Lean_Meta_Grind_simpCore___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5);
v___x_95_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__1, &l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1);
v___x_96_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__4, &l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4);
v___x_97_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_95_);
lean_ctor_set(v___x_97_, 3, v___x_94_);
lean_ctor_set(v___x_97_, 4, v___x_93_);
lean_ctor_set(v___x_97_, 5, v___x_92_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object* v_e_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_congrThms_110_; lean_object* v_simp_111_; lean_object* v_lastTag_112_; lean_object* v_issues_113_; lean_object* v_counters_114_; lean_object* v_splitDiags_115_; lean_object* v_lawfulEqCmpMap_116_; lean_object* v_reflCmpMap_117_; lean_object* v_anchors_118_; lean_object* v_instanceMap_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_168_; 
v___x_109_ = lean_st_ref_take(v___y_101_);
v_congrThms_110_ = lean_ctor_get(v___x_109_, 0);
v_simp_111_ = lean_ctor_get(v___x_109_, 1);
v_lastTag_112_ = lean_ctor_get(v___x_109_, 2);
v_issues_113_ = lean_ctor_get(v___x_109_, 3);
v_counters_114_ = lean_ctor_get(v___x_109_, 4);
v_splitDiags_115_ = lean_ctor_get(v___x_109_, 5);
v_lawfulEqCmpMap_116_ = lean_ctor_get(v___x_109_, 6);
v_reflCmpMap_117_ = lean_ctor_get(v___x_109_, 7);
v_anchors_118_ = lean_ctor_get(v___x_109_, 8);
v_instanceMap_119_ = lean_ctor_get(v___x_109_, 9);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_168_ == 0)
{
v___x_121_ = v___x_109_;
v_isShared_122_ = v_isSharedCheck_168_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_instanceMap_119_);
lean_inc(v_anchors_118_);
lean_inc(v_reflCmpMap_117_);
lean_inc(v_lawfulEqCmpMap_116_);
lean_inc(v_splitDiags_115_);
lean_inc(v_counters_114_);
lean_inc(v_issues_113_);
lean_inc(v_lastTag_112_);
lean_inc(v_simp_111_);
lean_inc(v_congrThms_110_);
lean_dec(v___x_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_168_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_congrThms_110_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_lastTag_112_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_issues_113_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_counters_114_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_splitDiags_115_);
lean_ctor_set(v_reuseFailAlloc_167_, 6, v_lawfulEqCmpMap_116_);
lean_ctor_set(v_reuseFailAlloc_167_, 7, v_reflCmpMap_117_);
lean_ctor_set(v_reuseFailAlloc_167_, 8, v_anchors_118_);
lean_ctor_set(v_reuseFailAlloc_167_, 9, v_instanceMap_119_);
v___x_125_ = v_reuseFailAlloc_167_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v_simp_127_; lean_object* v_simpMethods_128_; lean_object* v___x_129_; 
v___x_126_ = lean_st_ref_set(v___y_101_, v___x_125_);
v_simp_127_ = lean_ctor_get(v___y_100_, 0);
lean_inc_ref(v_simp_127_);
v_simpMethods_128_ = lean_ctor_get(v___y_100_, 1);
lean_inc_ref(v_simpMethods_128_);
lean_dec_ref(v___y_100_);
v___x_129_ = l_Lean_Meta_Simp_mainCore(v_e_98_, v_simp_127_, v_simp_111_, v_simpMethods_128_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_158_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_158_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_158_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_158_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v___x_136_; lean_object* v_congrThms_137_; lean_object* v_lastTag_138_; lean_object* v_issues_139_; lean_object* v_counters_140_; lean_object* v_splitDiags_141_; lean_object* v_lawfulEqCmpMap_142_; lean_object* v_reflCmpMap_143_; lean_object* v_anchors_144_; lean_object* v_instanceMap_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_156_; 
v_fst_134_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_fst_134_);
v_snd_135_ = lean_ctor_get(v_a_130_, 1);
lean_inc(v_snd_135_);
lean_dec(v_a_130_);
v___x_136_ = lean_st_ref_take(v___y_101_);
v_congrThms_137_ = lean_ctor_get(v___x_136_, 0);
v_lastTag_138_ = lean_ctor_get(v___x_136_, 2);
v_issues_139_ = lean_ctor_get(v___x_136_, 3);
v_counters_140_ = lean_ctor_get(v___x_136_, 4);
v_splitDiags_141_ = lean_ctor_get(v___x_136_, 5);
v_lawfulEqCmpMap_142_ = lean_ctor_get(v___x_136_, 6);
v_reflCmpMap_143_ = lean_ctor_get(v___x_136_, 7);
v_anchors_144_ = lean_ctor_get(v___x_136_, 8);
v_instanceMap_145_ = lean_ctor_get(v___x_136_, 9);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v___x_136_, 1);
lean_dec(v_unused_157_);
v___x_147_ = v___x_136_;
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_instanceMap_145_);
lean_inc(v_anchors_144_);
lean_inc(v_reflCmpMap_143_);
lean_inc(v_lawfulEqCmpMap_142_);
lean_inc(v_splitDiags_141_);
lean_inc(v_counters_140_);
lean_inc(v_issues_139_);
lean_inc(v_lastTag_138_);
lean_inc(v_congrThms_137_);
lean_dec(v___x_136_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_156_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v_snd_135_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_congrThms_137_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_snd_135_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_lastTag_138_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_issues_139_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_counters_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 5, v_splitDiags_141_);
lean_ctor_set(v_reuseFailAlloc_155_, 6, v_lawfulEqCmpMap_142_);
lean_ctor_set(v_reuseFailAlloc_155_, 7, v_reflCmpMap_143_);
lean_ctor_set(v_reuseFailAlloc_155_, 8, v_anchors_144_);
lean_ctor_set(v_reuseFailAlloc_155_, 9, v_instanceMap_145_);
v___x_150_ = v_reuseFailAlloc_155_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_st_ref_set(v___y_101_, v___x_150_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v_fst_134_);
v___x_153_ = v___x_132_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_fst_134_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_129_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_129_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object* v_e_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_Grind_simpCore___lam__0(v_e_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec(v___y_170_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_options_193_; lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_options_193_ = lean_ctor_get(v_a_190_, 2);
lean_inc_ref(v_options_193_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_194_, 0, v_e_182_);
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_simpCore___closed__0));
v___x_196_ = lean_box(0);
v___x_197_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_195_, v_options_193_, v___f_194_, v___x_196_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec_ref(v_options_193_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Grind_simpCore(v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* v_e_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_congrThms_222_; lean_object* v_simp_223_; lean_object* v_lastTag_224_; lean_object* v_issues_225_; lean_object* v_counters_226_; lean_object* v_splitDiags_227_; lean_object* v_lawfulEqCmpMap_228_; lean_object* v_reflCmpMap_229_; lean_object* v_anchors_230_; lean_object* v_instanceMap_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_282_; 
v___x_221_ = lean_st_ref_take(v___y_213_);
v_congrThms_222_ = lean_ctor_get(v___x_221_, 0);
v_simp_223_ = lean_ctor_get(v___x_221_, 1);
v_lastTag_224_ = lean_ctor_get(v___x_221_, 2);
v_issues_225_ = lean_ctor_get(v___x_221_, 3);
v_counters_226_ = lean_ctor_get(v___x_221_, 4);
v_splitDiags_227_ = lean_ctor_get(v___x_221_, 5);
v_lawfulEqCmpMap_228_ = lean_ctor_get(v___x_221_, 6);
v_reflCmpMap_229_ = lean_ctor_get(v___x_221_, 7);
v_anchors_230_ = lean_ctor_get(v___x_221_, 8);
v_instanceMap_231_ = lean_ctor_get(v___x_221_, 9);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_282_ == 0)
{
v___x_233_ = v___x_221_;
v_isShared_234_ = v_isSharedCheck_282_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_instanceMap_231_);
lean_inc(v_anchors_230_);
lean_inc(v_reflCmpMap_229_);
lean_inc(v_lawfulEqCmpMap_228_);
lean_inc(v_splitDiags_227_);
lean_inc(v_counters_226_);
lean_inc(v_issues_225_);
lean_inc(v_lastTag_224_);
lean_inc(v_simp_223_);
lean_inc(v_congrThms_222_);
lean_dec(v___x_221_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_282_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_unsigned_to_nat(32u);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
lean_dec_ref(v___x_236_);
v___x_237_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_congrThms_222_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_lastTag_224_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_issues_225_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_counters_226_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_splitDiags_227_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_lawfulEqCmpMap_228_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_reflCmpMap_229_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_anchors_230_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_instanceMap_231_);
v___x_239_ = v_reuseFailAlloc_281_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v_simp_241_; lean_object* v_simpMethods_242_; lean_object* v___x_243_; 
v___x_240_ = lean_st_ref_set(v___y_213_, v___x_239_);
v_simp_241_ = lean_ctor_get(v___y_212_, 0);
lean_inc_ref(v_simp_241_);
v_simpMethods_242_ = lean_ctor_get(v___y_212_, 1);
lean_inc_ref(v_simpMethods_242_);
lean_dec_ref(v___y_212_);
v___x_243_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_210_, v_simp_241_, v_simp_223_, v_simpMethods_242_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_272_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_272_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_272_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_250_; lean_object* v_congrThms_251_; lean_object* v_lastTag_252_; lean_object* v_issues_253_; lean_object* v_counters_254_; lean_object* v_splitDiags_255_; lean_object* v_lawfulEqCmpMap_256_; lean_object* v_reflCmpMap_257_; lean_object* v_anchors_258_; lean_object* v_instanceMap_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_fst_248_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_fst_248_);
v_snd_249_ = lean_ctor_get(v_a_244_, 1);
lean_inc(v_snd_249_);
lean_dec(v_a_244_);
v___x_250_ = lean_st_ref_take(v___y_213_);
v_congrThms_251_ = lean_ctor_get(v___x_250_, 0);
v_lastTag_252_ = lean_ctor_get(v___x_250_, 2);
v_issues_253_ = lean_ctor_get(v___x_250_, 3);
v_counters_254_ = lean_ctor_get(v___x_250_, 4);
v_splitDiags_255_ = lean_ctor_get(v___x_250_, 5);
v_lawfulEqCmpMap_256_ = lean_ctor_get(v___x_250_, 6);
v_reflCmpMap_257_ = lean_ctor_get(v___x_250_, 7);
v_anchors_258_ = lean_ctor_get(v___x_250_, 8);
v_instanceMap_259_ = lean_ctor_get(v___x_250_, 9);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_250_, 1);
lean_dec(v_unused_271_);
v___x_261_ = v___x_250_;
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_instanceMap_259_);
lean_inc(v_anchors_258_);
lean_inc(v_reflCmpMap_257_);
lean_inc(v_lawfulEqCmpMap_256_);
lean_inc(v_splitDiags_255_);
lean_inc(v_counters_254_);
lean_inc(v_issues_253_);
lean_inc(v_lastTag_252_);
lean_inc(v_congrThms_251_);
lean_dec(v___x_250_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_snd_249_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_congrThms_251_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_lastTag_252_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_issues_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_counters_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_splitDiags_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_lawfulEqCmpMap_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_reflCmpMap_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_anchors_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 9, v_instanceMap_259_);
v___x_264_ = v_reuseFailAlloc_269_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_st_ref_set(v___y_213_, v___x_264_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v_fst_248_);
v___x_267_ = v___x_246_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fst_248_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_243_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_243_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* v_e_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Grind_dsimpCore___lam__0(v_e_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec(v___y_284_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_options_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_options_307_ = lean_ctor_get(v_a_304_, 2);
lean_inc_ref(v_options_307_);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_308_, 0, v_e_296_);
v___x_309_ = ((lean_object*)(l_Lean_Meta_Grind_dsimpCore___closed__0));
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_309_, v_options_307_, v___f_308_, v___x_310_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec_ref(v_options_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_dsimpCore(v_e_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_324_, lean_object* v___y_325_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = l_Lean_Expr_hasMVar(v_e_324_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v_e_324_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v_mctx_330_; lean_object* v___x_331_; lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_334_; lean_object* v_cache_335_; lean_object* v_zetaDeltaFVarIds_336_; lean_object* v_postponed_337_; lean_object* v_diag_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_347_; 
v___x_329_ = lean_st_ref_get(v___y_325_);
v_mctx_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_330_);
lean_dec(v___x_329_);
v___x_331_ = l_Lean_instantiateMVarsCore(v_mctx_330_, v_e_324_);
v_fst_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_fst_332_);
v_snd_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc(v_snd_333_);
lean_dec_ref(v___x_331_);
v___x_334_ = lean_st_ref_take(v___y_325_);
v_cache_335_ = lean_ctor_get(v___x_334_, 1);
v_zetaDeltaFVarIds_336_ = lean_ctor_get(v___x_334_, 2);
v_postponed_337_ = lean_ctor_get(v___x_334_, 3);
v_diag_338_ = lean_ctor_get(v___x_334_, 4);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v___x_334_, 0);
lean_dec(v_unused_348_);
v___x_340_ = v___x_334_;
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_diag_338_);
lean_inc(v_postponed_337_);
lean_inc(v_zetaDeltaFVarIds_336_);
lean_inc(v_cache_335_);
lean_dec(v___x_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_snd_333_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_snd_333_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_cache_335_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_zetaDeltaFVarIds_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_postponed_337_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_diag_338_);
v___x_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_st_ref_set(v___y_325_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_fst_332_);
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_349_, v___y_350_);
lean_dec(v___y_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_353_, v___y_361_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec(v___y_367_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_options_385_; uint8_t v_hasTrace_386_; 
v_options_385_ = lean_ctor_get(v___y_383_, 2);
v_hasTrace_386_ = lean_ctor_get_uint8(v_options_385_, sizeof(void*)*1);
if (v_hasTrace_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_cls_382_);
v___x_387_ = lean_box(v_hasTrace_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v_inheritedTraceOptions_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_inheritedTraceOptions_389_ = lean_ctor_get(v___y_383_, 13);
v___x_390_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_391_ = l_Lean_Name_append(v___x_390_, v_cls_382_);
v___x_392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_389_, v_options_385_, v___x_391_);
lean_dec(v___x_391_);
v___x_393_ = lean_box(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_395_, v___y_396_);
lean_dec_ref(v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_399_, v___y_408_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec(v___y_413_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2(lean_object* v_msgData_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; lean_object* v_env_432_; lean_object* v___x_433_; lean_object* v_mctx_434_; lean_object* v_lctx_435_; lean_object* v_options_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_431_ = lean_st_ref_get(v___y_429_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
v___x_433_ = lean_st_ref_get(v___y_427_);
v_mctx_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_mctx_434_);
lean_dec(v___x_433_);
v_lctx_435_ = lean_ctor_get(v___y_426_, 2);
v_options_436_ = lean_ctor_get(v___y_428_, 2);
lean_inc_ref(v_options_436_);
lean_inc_ref(v_lctx_435_);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v_env_432_);
lean_ctor_set(v___x_437_, 1, v_mctx_434_);
lean_ctor_set(v___x_437_, 2, v_lctx_435_);
lean_ctor_set(v___x_437_, 3, v_options_436_);
v___x_438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_msgData_425_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2___boxed(lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2(v_msgData_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_447_; double v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_float_of_nat(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(lean_object* v_cls_452_, lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_ref_459_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_505_; 
v_ref_459_ = lean_ctor_get(v___y_456_, 5);
v___x_460_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2_spec__2(v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_505_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_505_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_505_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v_traceState_466_; lean_object* v_env_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_cache_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_504_; 
v___x_465_ = lean_st_ref_take(v___y_457_);
v_traceState_466_ = lean_ctor_get(v___x_465_, 4);
v_env_467_ = lean_ctor_get(v___x_465_, 0);
v_nextMacroScope_468_ = lean_ctor_get(v___x_465_, 1);
v_ngen_469_ = lean_ctor_get(v___x_465_, 2);
v_auxDeclNGen_470_ = lean_ctor_get(v___x_465_, 3);
v_cache_471_ = lean_ctor_get(v___x_465_, 5);
v_messages_472_ = lean_ctor_get(v___x_465_, 6);
v_infoState_473_ = lean_ctor_get(v___x_465_, 7);
v_snapshotTasks_474_ = lean_ctor_get(v___x_465_, 8);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_504_ == 0)
{
v___x_476_ = v___x_465_;
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snapshotTasks_474_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_472_);
lean_inc(v_cache_471_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_470_);
lean_inc(v_ngen_469_);
lean_inc(v_nextMacroScope_468_);
lean_inc(v_env_467_);
lean_dec(v___x_465_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint64_t v_tid_478_; lean_object* v_traces_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_503_; 
v_tid_478_ = lean_ctor_get_uint64(v_traceState_466_, sizeof(void*)*1);
v_traces_479_ = lean_ctor_get(v_traceState_466_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_traceState_466_);
if (v_isSharedCheck_503_ == 0)
{
v___x_481_ = v_traceState_466_;
v_isShared_482_ = v_isSharedCheck_503_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_traces_479_);
lean_dec(v_traceState_466_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_503_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; double v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__0);
v___x_485_ = 0;
v___x_486_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__1));
v___x_487_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_487_, 0, v_cls_452_);
lean_ctor_set(v___x_487_, 1, v___x_483_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
lean_ctor_set_float(v___x_487_, sizeof(void*)*3, v___x_484_);
lean_ctor_set_float(v___x_487_, sizeof(void*)*3 + 8, v___x_484_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*3 + 16, v___x_485_);
v___x_488_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___closed__2));
v___x_489_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v_a_461_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
lean_inc(v_ref_459_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_ref_459_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_PersistentArray_push___redArg(v_traces_479_, v___x_490_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_491_);
v___x_493_ = v___x_481_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_491_);
lean_ctor_set_uint64(v_reuseFailAlloc_502_, sizeof(void*)*1, v_tid_478_);
v___x_493_ = v_reuseFailAlloc_502_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_493_);
v___x_495_ = v___x_476_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_env_467_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_nextMacroScope_468_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_ngen_469_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v_cache_471_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_snapshotTasks_474_);
v___x_495_ = v_reuseFailAlloc_501_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = lean_st_ref_set(v___y_457_, v___x_495_);
v___x_497_ = lean_box(0);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_497_);
v___x_499_ = v___x_463_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg___boxed(lean_object* v_cls_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(v_cls_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__4(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__3));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; lean_object* v_a_535_; lean_object* v___x_536_; 
v___x_534_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_522_, v_a_530_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref(v___x_534_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
lean_inc(v_a_535_);
v___x_536_ = l_Lean_Meta_Grind_simpCore(v_a_535_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_expr_538_; lean_object* v___x_539_; lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref(v___x_536_);
v_expr_538_ = lean_ctor_get(v_a_537_, 0);
lean_inc_ref(v_expr_538_);
v___x_539_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_538_, v_a_530_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
v___x_541_ = l_Lean_Meta_Sym_unfoldReducible(v_a_540_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
v___x_543_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_542_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
v___x_545_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_544_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_547_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_546_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
v___x_549_ = l_Lean_Meta_Grind_foldProjs(v_a_548_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_551_ = l_Lean_Meta_Sym_normalizeLevels(v_a_550_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref(v___x_551_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
v___x_553_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_552_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_554_);
v___x_555_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_537_, v_a_554_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_expr_557_; lean_object* v___x_558_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v_expr_557_ = lean_ctor_get(v_a_554_, 0);
lean_inc_ref(v_expr_557_);
lean_dec(v_a_554_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
v___x_558_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_557_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v___x_558_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_559_);
v___x_560_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_556_, v_a_559_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_expr_562_; lean_object* v___x_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___x_560_);
v_expr_562_ = lean_ctor_get(v_a_559_, 0);
lean_inc_ref(v_expr_562_);
lean_dec(v_a_559_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
lean_inc(v_a_523_);
v___x_563_ = lean_grind_canon(v_expr_562_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_564_, v_a_528_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_611_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_611_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_611_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_611_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_a_586_; uint8_t v___x_587_; 
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_585_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_584_, v_a_531_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
v___x_587_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_587_ == 0)
{
lean_dec(v_a_535_);
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
goto v___jp_570_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_updateLastTag(v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v___x_588_);
v___x_589_ = l_Lean_MessageData_ofExpr(v_a_535_);
v___x_590_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__4, &l_Lean_Meta_Grind_preprocessImpl___closed__4_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__4);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc(v_a_566_);
v___x_592_ = l_Lean_MessageData_ofExpr(v_a_566_);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(v___x_584_, v___x_593_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_dec_ref(v___x_594_);
goto v___jp_570_;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_del_object(v___x_568_);
lean_dec(v_a_566_);
lean_dec(v_a_561_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_568_);
lean_dec(v_a_566_);
lean_dec(v_a_561_);
lean_dec(v_a_535_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
v_a_603_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_588_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_588_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
v___jp_570_:
{
lean_object* v_proof_x3f_571_; uint8_t v_cache_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v_proof_x3f_571_ = lean_ctor_get(v_a_561_, 1);
v_cache_572_ = lean_ctor_get_uint8(v_a_561_, sizeof(void*)*2);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_a_561_, 0);
lean_dec(v_unused_583_);
v___x_574_ = v_a_561_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_proof_x3f_571_);
lean_dec(v_a_561_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v_a_566_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_566_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_proof_x3f_571_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*2, v_cache_572_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_577_);
v___x_579_ = v___x_568_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_561_);
lean_dec(v_a_535_);
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
v_a_612_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_565_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_565_);
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
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_561_);
lean_dec(v_a_535_);
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
v_a_620_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_563_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_563_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_dec(v_a_559_);
lean_dec(v_a_535_);
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
return v___x_560_;
}
}
else
{
lean_dec(v_a_556_);
lean_dec(v_a_535_);
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
return v___x_558_;
}
}
else
{
lean_dec(v_a_554_);
lean_dec(v_a_535_);
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
return v___x_555_;
}
}
else
{
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
return v___x_553_;
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_628_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_551_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_551_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
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
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_636_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_549_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_549_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_644_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_547_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_547_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_652_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_545_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_545_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_660_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_543_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_543_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
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
v_a_668_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_541_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_541_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_dec(v_a_535_);
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
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = lean_grind_preprocess(v_e_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2(lean_object* v_cls_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(v_cls_689_, v_msg_690_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___boxed(lean_object* v_cls_703_, lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2(v_cls_703_, v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec(v___y_705_);
return v_res_716_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__3));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_735_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__7));
v___x_736_ = l_Lean_mkConst(v___x_735_, v___x_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_737_, lean_object* v_proof_738_, lean_object* v_generation_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
lean_inc(v_a_749_);
lean_inc_ref(v_a_748_);
lean_inc(v_a_747_);
lean_inc_ref(v_a_746_);
lean_inc(v_a_740_);
lean_inc_ref(v_prop_737_);
v___x_751_ = lean_grind_preprocess(v_prop_737_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_819_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_819_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_819_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_819_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_expr_756_; lean_object* v_proof_x3f_757_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_805_; 
v_expr_756_ = lean_ctor_get(v_a_752_, 0);
lean_inc_ref(v_expr_756_);
v_proof_x3f_757_ = lean_ctor_get(v_a_752_, 1);
lean_inc(v_proof_x3f_757_);
lean_dec(v_a_752_);
if (lean_obj_tag(v_proof_x3f_757_) == 1)
{
lean_object* v_val_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_val_816_ = lean_ctor_get(v_proof_x3f_757_, 0);
lean_inc(v_val_816_);
lean_dec_ref(v_proof_x3f_757_);
v___x_817_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__9, &l_Lean_Meta_Grind_pushNewFact_x27___closed__9_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9);
lean_inc_ref(v_expr_756_);
lean_inc_ref(v_prop_737_);
v___x_818_ = l_Lean_mkApp4(v___x_817_, v_prop_737_, v_expr_756_, v_val_816_, v_proof_738_);
v___y_805_ = v___x_818_;
goto v___jp_804_;
}
else
{
lean_dec(v_proof_x3f_757_);
v___y_805_ = v_proof_738_;
goto v___jp_804_;
}
v___jp_758_:
{
lean_object* v___x_761_; lean_object* v_toGoalState_762_; lean_object* v_mvarId_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_803_; 
v___x_761_ = lean_st_ref_take(v___y_760_);
v_toGoalState_762_ = lean_ctor_get(v___x_761_, 0);
v_mvarId_763_ = lean_ctor_get(v___x_761_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_803_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_803_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_mvarId_763_);
lean_inc(v_toGoalState_762_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_803_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_nextDeclIdx_767_; lean_object* v_canon_768_; lean_object* v_enodeMap_769_; lean_object* v_exprs_770_; lean_object* v_parents_771_; lean_object* v_congrTable_772_; lean_object* v_appMap_773_; lean_object* v_indicesFound_774_; lean_object* v_newFacts_775_; uint8_t v_inconsistent_776_; lean_object* v_nextIdx_777_; lean_object* v_newRawFacts_778_; lean_object* v_facts_779_; lean_object* v_extThms_780_; lean_object* v_ematch_781_; lean_object* v_inj_782_; lean_object* v_split_783_; lean_object* v_clean_784_; lean_object* v_sstates_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_802_; 
v_nextDeclIdx_767_ = lean_ctor_get(v_toGoalState_762_, 0);
v_canon_768_ = lean_ctor_get(v_toGoalState_762_, 1);
v_enodeMap_769_ = lean_ctor_get(v_toGoalState_762_, 2);
v_exprs_770_ = lean_ctor_get(v_toGoalState_762_, 3);
v_parents_771_ = lean_ctor_get(v_toGoalState_762_, 4);
v_congrTable_772_ = lean_ctor_get(v_toGoalState_762_, 5);
v_appMap_773_ = lean_ctor_get(v_toGoalState_762_, 6);
v_indicesFound_774_ = lean_ctor_get(v_toGoalState_762_, 7);
v_newFacts_775_ = lean_ctor_get(v_toGoalState_762_, 8);
v_inconsistent_776_ = lean_ctor_get_uint8(v_toGoalState_762_, sizeof(void*)*18);
v_nextIdx_777_ = lean_ctor_get(v_toGoalState_762_, 9);
v_newRawFacts_778_ = lean_ctor_get(v_toGoalState_762_, 10);
v_facts_779_ = lean_ctor_get(v_toGoalState_762_, 11);
v_extThms_780_ = lean_ctor_get(v_toGoalState_762_, 12);
v_ematch_781_ = lean_ctor_get(v_toGoalState_762_, 13);
v_inj_782_ = lean_ctor_get(v_toGoalState_762_, 14);
v_split_783_ = lean_ctor_get(v_toGoalState_762_, 15);
v_clean_784_ = lean_ctor_get(v_toGoalState_762_, 16);
v_sstates_785_ = lean_ctor_get(v_toGoalState_762_, 17);
v_isSharedCheck_802_ = !lean_is_exclusive(v_toGoalState_762_);
if (v_isSharedCheck_802_ == 0)
{
v___x_787_ = v_toGoalState_762_;
v_isShared_788_ = v_isSharedCheck_802_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_sstates_785_);
lean_inc(v_clean_784_);
lean_inc(v_split_783_);
lean_inc(v_inj_782_);
lean_inc(v_ematch_781_);
lean_inc(v_extThms_780_);
lean_inc(v_facts_779_);
lean_inc(v_newRawFacts_778_);
lean_inc(v_nextIdx_777_);
lean_inc(v_newFacts_775_);
lean_inc(v_indicesFound_774_);
lean_inc(v_appMap_773_);
lean_inc(v_congrTable_772_);
lean_inc(v_parents_771_);
lean_inc(v_exprs_770_);
lean_inc(v_enodeMap_769_);
lean_inc(v_canon_768_);
lean_inc(v_nextDeclIdx_767_);
lean_dec(v_toGoalState_762_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_802_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v_expr_756_);
lean_ctor_set(v___x_789_, 1, v___y_759_);
lean_ctor_set(v___x_789_, 2, v_generation_739_);
v___x_790_ = lean_array_push(v_newFacts_775_, v___x_789_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 8, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_nextDeclIdx_767_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_canon_768_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_enodeMap_769_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_exprs_770_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_parents_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_congrTable_772_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_appMap_773_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_indicesFound_774_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_801_, 9, v_nextIdx_777_);
lean_ctor_set(v_reuseFailAlloc_801_, 10, v_newRawFacts_778_);
lean_ctor_set(v_reuseFailAlloc_801_, 11, v_facts_779_);
lean_ctor_set(v_reuseFailAlloc_801_, 12, v_extThms_780_);
lean_ctor_set(v_reuseFailAlloc_801_, 13, v_ematch_781_);
lean_ctor_set(v_reuseFailAlloc_801_, 14, v_inj_782_);
lean_ctor_set(v_reuseFailAlloc_801_, 15, v_split_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 16, v_clean_784_);
lean_ctor_set(v_reuseFailAlloc_801_, 17, v_sstates_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_801_, sizeof(void*)*18, v_inconsistent_776_);
v___x_792_ = v_reuseFailAlloc_801_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_792_);
v___x_794_ = v___x_765_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_mvarId_763_);
v___x_794_ = v_reuseFailAlloc_800_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_795_ = lean_st_ref_set(v___y_760_, v___x_794_);
lean_dec(v___y_760_);
v___x_796_ = lean_box(0);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_796_);
v___x_798_ = v___x_754_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
v___jp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_a_808_; uint8_t v___x_809_; 
v___x_806_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_807_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_806_, v_a_748_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v___x_809_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_809_ == 0)
{
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec_ref(v_prop_737_);
v___y_759_ = v___y_805_;
v___y_760_ = v_a_740_;
goto v___jp_758_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_810_ = l_Lean_MessageData_ofExpr(v_prop_737_);
v___x_811_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__4, &l_Lean_Meta_Grind_pushNewFact_x27___closed__4_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
lean_inc_ref(v_expr_756_);
v___x_813_ = l_Lean_MessageData_ofExpr(v_expr_756_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(v___x_806_, v___x_814_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref(v___x_815_);
v___y_759_ = v___y_805_;
v___y_760_ = v_a_740_;
goto v___jp_758_;
}
else
{
lean_dec_ref(v___y_805_);
lean_dec_ref(v_expr_756_);
lean_del_object(v___x_754_);
lean_dec(v_a_740_);
lean_dec(v_generation_739_);
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_740_);
lean_dec(v_generation_739_);
lean_dec_ref(v_proof_738_);
lean_dec_ref(v_prop_737_);
v_a_820_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_751_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_751_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_828_, lean_object* v_proof_829_, lean_object* v_generation_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_828_, v_proof_829_, v_generation_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_843_, lean_object* v_generation_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_856_; 
lean_inc(v_a_854_);
lean_inc_ref(v_a_853_);
lean_inc(v_a_852_);
lean_inc_ref(v_a_851_);
lean_inc_ref(v_proof_843_);
v___x_856_ = lean_infer_type(v_proof_843_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_a_860_; uint8_t v___x_861_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_859_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_858_, v_a_853_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_857_, v_proof_843_, v_generation_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc(v_a_857_);
v___x_863_ = l_Lean_MessageData_ofExpr(v_a_857_);
v___x_864_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__2___redArg(v___x_858_, v___x_863_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v___x_864_);
v___x_865_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_857_, v_proof_843_, v_generation_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_865_;
}
else
{
lean_dec(v_a_857_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_generation_844_);
lean_dec_ref(v_proof_843_);
return v___x_864_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_generation_844_);
lean_dec_ref(v_proof_843_);
v_a_866_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_856_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_856_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_874_, lean_object* v_generation_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Grind_pushNewFact(v_proof_874_, v_generation_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v_a_901_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_888_, v_a_896_);
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
v___x_902_ = l_Lean_Meta_Sym_unfoldReducible(v_a_901_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
v___x_904_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_903_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_904_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
v___x_906_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_905_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
v___x_908_ = l_Lean_Meta_Grind_foldProjs(v_a_907_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
v___x_910_ = l_Lean_Meta_Sym_normalizeLevels(v_a_909_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
lean_inc(v_a_894_);
v___x_912_ = lean_grind_canon(v_a_911_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_912_);
v___x_914_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_913_, v_a_894_);
lean_dec(v_a_894_);
return v___x_914_;
}
else
{
lean_dec(v_a_894_);
return v___x_912_;
}
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
return v___x_910_;
}
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
return v___x_908_;
}
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
return v___x_906_;
}
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
return v___x_904_;
}
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_Grind_preprocessLight(v_e_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v_res_927_;
}
}
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
}
#ifdef __cplusplus
}
#endif

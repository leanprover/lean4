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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Simp_dsimpMainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_preprocessImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 174, 175, 152, 201, 92, 177, 229)}};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_preprocessImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_preprocessImpl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__5;
static const lean_string_object l_Lean_Meta_Grind_preprocessImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_preprocessImpl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_preprocessImpl___closed__7;
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pushNewFact"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_preprocessImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 237, 7, 223, 90, 130, 102, 106)}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__3;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " ==> "};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__5;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNewFact_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_pushNewFact_x27___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(lean_object* v_category_1_, lean_object* v_opts_2_, lean_object* v_act_3_, lean_object* v_decl_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
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
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
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
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
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
lean_object* v___x_109_; lean_object* v_congrThms_110_; lean_object* v_simp_111_; lean_object* v_lastTag_112_; lean_object* v_counters_113_; lean_object* v_splitDiags_114_; lean_object* v_lawfulEqCmpMap_115_; lean_object* v_reflCmpMap_116_; lean_object* v_anchors_117_; lean_object* v_instanceMap_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_166_; 
v___x_109_ = lean_st_ref_take(v___y_101_);
v_congrThms_110_ = lean_ctor_get(v___x_109_, 0);
v_simp_111_ = lean_ctor_get(v___x_109_, 1);
v_lastTag_112_ = lean_ctor_get(v___x_109_, 2);
v_counters_113_ = lean_ctor_get(v___x_109_, 3);
v_splitDiags_114_ = lean_ctor_get(v___x_109_, 4);
v_lawfulEqCmpMap_115_ = lean_ctor_get(v___x_109_, 5);
v_reflCmpMap_116_ = lean_ctor_get(v___x_109_, 6);
v_anchors_117_ = lean_ctor_get(v___x_109_, 7);
v_instanceMap_118_ = lean_ctor_get(v___x_109_, 8);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_166_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_166_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_instanceMap_118_);
lean_inc(v_anchors_117_);
lean_inc(v_reflCmpMap_116_);
lean_inc(v_lawfulEqCmpMap_115_);
lean_inc(v_splitDiags_114_);
lean_inc(v_counters_113_);
lean_inc(v_lastTag_112_);
lean_inc(v_simp_111_);
lean_inc(v_congrThms_110_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_166_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_congrThms_110_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_lastTag_112_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_counters_113_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_splitDiags_114_);
lean_ctor_set(v_reuseFailAlloc_165_, 5, v_lawfulEqCmpMap_115_);
lean_ctor_set(v_reuseFailAlloc_165_, 6, v_reflCmpMap_116_);
lean_ctor_set(v_reuseFailAlloc_165_, 7, v_anchors_117_);
lean_ctor_set(v_reuseFailAlloc_165_, 8, v_instanceMap_118_);
v___x_124_ = v_reuseFailAlloc_165_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v_simp_126_; lean_object* v_simpMethods_127_; lean_object* v___x_128_; 
v___x_125_ = lean_st_ref_set(v___y_101_, v___x_124_);
v_simp_126_ = lean_ctor_get(v___y_100_, 0);
v_simpMethods_127_ = lean_ctor_get(v___y_100_, 1);
lean_inc_ref(v_simpMethods_127_);
lean_inc_ref(v_simp_126_);
v___x_128_ = l_Lean_Meta_Simp_mainCore(v_e_98_, v_simp_126_, v_simp_111_, v_simpMethods_127_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_156_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_156_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_156_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_156_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_135_; lean_object* v_congrThms_136_; lean_object* v_lastTag_137_; lean_object* v_counters_138_; lean_object* v_splitDiags_139_; lean_object* v_lawfulEqCmpMap_140_; lean_object* v_reflCmpMap_141_; lean_object* v_anchors_142_; lean_object* v_instanceMap_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_154_; 
v_fst_133_ = lean_ctor_get(v_a_129_, 0);
lean_inc(v_fst_133_);
v_snd_134_ = lean_ctor_get(v_a_129_, 1);
lean_inc(v_snd_134_);
lean_dec(v_a_129_);
v___x_135_ = lean_st_ref_take(v___y_101_);
v_congrThms_136_ = lean_ctor_get(v___x_135_, 0);
v_lastTag_137_ = lean_ctor_get(v___x_135_, 2);
v_counters_138_ = lean_ctor_get(v___x_135_, 3);
v_splitDiags_139_ = lean_ctor_get(v___x_135_, 4);
v_lawfulEqCmpMap_140_ = lean_ctor_get(v___x_135_, 5);
v_reflCmpMap_141_ = lean_ctor_get(v___x_135_, 6);
v_anchors_142_ = lean_ctor_get(v___x_135_, 7);
v_instanceMap_143_ = lean_ctor_get(v___x_135_, 8);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v___x_135_, 1);
lean_dec(v_unused_155_);
v___x_145_ = v___x_135_;
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_instanceMap_143_);
lean_inc(v_anchors_142_);
lean_inc(v_reflCmpMap_141_);
lean_inc(v_lawfulEqCmpMap_140_);
lean_inc(v_splitDiags_139_);
lean_inc(v_counters_138_);
lean_inc(v_lastTag_137_);
lean_inc(v_congrThms_136_);
lean_dec(v___x_135_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_snd_134_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_congrThms_136_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_snd_134_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_lastTag_137_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_counters_138_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v_splitDiags_139_);
lean_ctor_set(v_reuseFailAlloc_153_, 5, v_lawfulEqCmpMap_140_);
lean_ctor_set(v_reuseFailAlloc_153_, 6, v_reflCmpMap_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 7, v_anchors_142_);
lean_ctor_set(v_reuseFailAlloc_153_, 8, v_instanceMap_143_);
v___x_148_ = v_reuseFailAlloc_153_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_st_ref_set(v___y_101_, v___x_148_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v_fst_133_);
v___x_151_ = v___x_131_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_133_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_128_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_128_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object* v_e_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_Grind_simpCore___lam__0(v_e_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_options_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_options_191_ = lean_ctor_get(v_a_188_, 2);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_192_, 0, v_e_180_);
v___x_193_ = ((lean_object*)(l_Lean_Meta_Grind_simpCore___closed__0));
v___x_194_ = lean_box(0);
v___x_195_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_193_, v_options_191_, v___f_192_, v___x_194_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_Grind_simpCore(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* v_e_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_congrThms_220_; lean_object* v_simp_221_; lean_object* v_lastTag_222_; lean_object* v_counters_223_; lean_object* v_splitDiags_224_; lean_object* v_lawfulEqCmpMap_225_; lean_object* v_reflCmpMap_226_; lean_object* v_anchors_227_; lean_object* v_instanceMap_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_278_; 
v___x_219_ = lean_st_ref_take(v___y_211_);
v_congrThms_220_ = lean_ctor_get(v___x_219_, 0);
v_simp_221_ = lean_ctor_get(v___x_219_, 1);
v_lastTag_222_ = lean_ctor_get(v___x_219_, 2);
v_counters_223_ = lean_ctor_get(v___x_219_, 3);
v_splitDiags_224_ = lean_ctor_get(v___x_219_, 4);
v_lawfulEqCmpMap_225_ = lean_ctor_get(v___x_219_, 5);
v_reflCmpMap_226_ = lean_ctor_get(v___x_219_, 6);
v_anchors_227_ = lean_ctor_get(v___x_219_, 7);
v_instanceMap_228_ = lean_ctor_get(v___x_219_, 8);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_278_ == 0)
{
v___x_230_ = v___x_219_;
v_isShared_231_ = v_isSharedCheck_278_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_instanceMap_228_);
lean_inc(v_anchors_227_);
lean_inc(v_reflCmpMap_226_);
lean_inc(v_lawfulEqCmpMap_225_);
lean_inc(v_splitDiags_224_);
lean_inc(v_counters_223_);
lean_inc(v_lastTag_222_);
lean_inc(v_simp_221_);
lean_inc(v_congrThms_220_);
lean_dec(v___x_219_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_278_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(32u);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
lean_dec_ref(v___x_233_);
v___x_234_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_234_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_congrThms_220_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_lastTag_222_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_counters_223_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_splitDiags_224_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_lawfulEqCmpMap_225_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_reflCmpMap_226_);
lean_ctor_set(v_reuseFailAlloc_277_, 7, v_anchors_227_);
lean_ctor_set(v_reuseFailAlloc_277_, 8, v_instanceMap_228_);
v___x_236_ = v_reuseFailAlloc_277_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v_simp_238_; lean_object* v_simpMethods_239_; lean_object* v___x_240_; 
v___x_237_ = lean_st_ref_set(v___y_211_, v___x_236_);
v_simp_238_ = lean_ctor_get(v___y_210_, 0);
v_simpMethods_239_ = lean_ctor_get(v___y_210_, 1);
lean_inc_ref(v_simpMethods_239_);
lean_inc_ref(v_simp_238_);
v___x_240_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_208_, v_simp_238_, v_simp_221_, v_simpMethods_239_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_268_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_268_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_268_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_268_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_247_; lean_object* v_congrThms_248_; lean_object* v_lastTag_249_; lean_object* v_counters_250_; lean_object* v_splitDiags_251_; lean_object* v_lawfulEqCmpMap_252_; lean_object* v_reflCmpMap_253_; lean_object* v_anchors_254_; lean_object* v_instanceMap_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_266_; 
v_fst_245_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_fst_245_);
v_snd_246_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_snd_246_);
lean_dec(v_a_241_);
v___x_247_ = lean_st_ref_take(v___y_211_);
v_congrThms_248_ = lean_ctor_get(v___x_247_, 0);
v_lastTag_249_ = lean_ctor_get(v___x_247_, 2);
v_counters_250_ = lean_ctor_get(v___x_247_, 3);
v_splitDiags_251_ = lean_ctor_get(v___x_247_, 4);
v_lawfulEqCmpMap_252_ = lean_ctor_get(v___x_247_, 5);
v_reflCmpMap_253_ = lean_ctor_get(v___x_247_, 6);
v_anchors_254_ = lean_ctor_get(v___x_247_, 7);
v_instanceMap_255_ = lean_ctor_get(v___x_247_, 8);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_247_, 1);
lean_dec(v_unused_267_);
v___x_257_ = v___x_247_;
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_instanceMap_255_);
lean_inc(v_anchors_254_);
lean_inc(v_reflCmpMap_253_);
lean_inc(v_lawfulEqCmpMap_252_);
lean_inc(v_splitDiags_251_);
lean_inc(v_counters_250_);
lean_inc(v_lastTag_249_);
lean_inc(v_congrThms_248_);
lean_dec(v___x_247_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v_snd_246_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_congrThms_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_snd_246_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_lastTag_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_counters_250_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_splitDiags_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_lawfulEqCmpMap_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v_reflCmpMap_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_anchors_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v_instanceMap_255_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_st_ref_set(v___y_211_, v___x_260_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_fst_245_);
v___x_263_ = v___x_243_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_fst_245_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_240_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_240_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* v_e_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_dsimpCore___lam__0(v_e_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_options_303_; lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_options_303_ = lean_ctor_get(v_a_300_, 2);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_304_, 0, v_e_292_);
v___x_305_ = ((lean_object*)(l_Lean_Meta_Grind_dsimpCore___closed__0));
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_305_, v_options_303_, v___f_304_, v___x_306_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Grind_dsimpCore(v_e_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_320_, lean_object* v___y_321_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Expr_hasMVar(v_e_320_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_e_320_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v_mctx_326_; lean_object* v___x_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; lean_object* v_cache_331_; lean_object* v_zetaDeltaFVarIds_332_; lean_object* v_postponed_333_; lean_object* v_diag_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_343_; 
v___x_325_ = lean_st_ref_get(v___y_321_);
v_mctx_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_mctx_326_);
lean_dec(v___x_325_);
v___x_327_ = l_Lean_instantiateMVarsCore(v_mctx_326_, v_e_320_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v___x_327_);
v___x_330_ = lean_st_ref_take(v___y_321_);
v_cache_331_ = lean_ctor_get(v___x_330_, 1);
v_zetaDeltaFVarIds_332_ = lean_ctor_get(v___x_330_, 2);
v_postponed_333_ = lean_ctor_get(v___x_330_, 3);
v_diag_334_ = lean_ctor_get(v___x_330_, 4);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_344_);
v___x_336_ = v___x_330_;
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_diag_334_);
lean_inc(v_postponed_333_);
lean_inc(v_zetaDeltaFVarIds_332_);
lean_inc(v_cache_331_);
lean_dec(v___x_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_343_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v_snd_329_);
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_snd_329_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_cache_331_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_zetaDeltaFVarIds_332_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_postponed_333_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_diag_334_);
v___x_339_ = v_reuseFailAlloc_342_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_st_ref_set(v___y_321_, v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_fst_328_);
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_345_, v___y_346_);
lean_dec(v___y_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_349_, v___y_357_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_env_382_; lean_object* v___x_383_; lean_object* v_mctx_384_; lean_object* v_lctx_385_; lean_object* v_options_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_381_ = lean_st_ref_get(v___y_379_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_381_);
v___x_383_ = lean_st_ref_get(v___y_377_);
v_mctx_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_mctx_384_);
lean_dec(v___x_383_);
v_lctx_385_ = lean_ctor_get(v___y_376_, 2);
v_options_386_ = lean_ctor_get(v___y_378_, 2);
lean_inc_ref(v_options_386_);
lean_inc_ref(v_lctx_385_);
v___x_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_387_, 0, v_env_382_);
lean_ctor_set(v___x_387_, 1, v_mctx_384_);
lean_ctor_set(v___x_387_, 2, v_lctx_385_);
lean_ctor_set(v___x_387_, 3, v_options_386_);
v___x_388_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_msgData_375_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_397_; double v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_float_of_nat(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_ref_409_; lean_object* v___x_410_; lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_455_; 
v_ref_409_ = lean_ctor_get(v___y_406_, 5);
v___x_410_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_455_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_455_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_455_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v_traceState_416_; lean_object* v_env_417_; lean_object* v_nextMacroScope_418_; lean_object* v_ngen_419_; lean_object* v_auxDeclNGen_420_; lean_object* v_cache_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_454_; 
v___x_415_ = lean_st_ref_take(v___y_407_);
v_traceState_416_ = lean_ctor_get(v___x_415_, 4);
v_env_417_ = lean_ctor_get(v___x_415_, 0);
v_nextMacroScope_418_ = lean_ctor_get(v___x_415_, 1);
v_ngen_419_ = lean_ctor_get(v___x_415_, 2);
v_auxDeclNGen_420_ = lean_ctor_get(v___x_415_, 3);
v_cache_421_ = lean_ctor_get(v___x_415_, 5);
v_messages_422_ = lean_ctor_get(v___x_415_, 6);
v_infoState_423_ = lean_ctor_get(v___x_415_, 7);
v_snapshotTasks_424_ = lean_ctor_get(v___x_415_, 8);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_454_ == 0)
{
v___x_426_ = v___x_415_;
v_isShared_427_ = v_isSharedCheck_454_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_cache_421_);
lean_inc(v_traceState_416_);
lean_inc(v_auxDeclNGen_420_);
lean_inc(v_ngen_419_);
lean_inc(v_nextMacroScope_418_);
lean_inc(v_env_417_);
lean_dec(v___x_415_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_454_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint64_t v_tid_428_; lean_object* v_traces_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_453_; 
v_tid_428_ = lean_ctor_get_uint64(v_traceState_416_, sizeof(void*)*1);
v_traces_429_ = lean_ctor_get(v_traceState_416_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_traceState_416_);
if (v_isSharedCheck_453_ == 0)
{
v___x_431_ = v_traceState_416_;
v_isShared_432_ = v_isSharedCheck_453_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_traces_429_);
lean_dec(v_traceState_416_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_453_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; double v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_435_ = 0;
v___x_436_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_437_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_437_, 0, v_cls_402_);
lean_ctor_set(v___x_437_, 1, v___x_433_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set_float(v___x_437_, sizeof(void*)*3, v___x_434_);
lean_ctor_set_float(v___x_437_, sizeof(void*)*3 + 8, v___x_434_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*3 + 16, v___x_435_);
v___x_438_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_439_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v_a_411_);
lean_ctor_set(v___x_439_, 2, v___x_438_);
lean_inc(v_ref_409_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_ref_409_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_PersistentArray_push___redArg(v_traces_429_, v___x_440_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_441_);
v___x_443_ = v___x_431_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_441_);
lean_ctor_set_uint64(v_reuseFailAlloc_452_, sizeof(void*)*1, v_tid_428_);
v___x_443_ = v_reuseFailAlloc_452_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 4, v___x_443_);
v___x_445_ = v___x_426_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_env_417_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ngen_419_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_420_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_cache_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_messages_422_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_snapshotTasks_424_);
v___x_445_ = v_reuseFailAlloc_451_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_446_ = lean_st_ref_set(v___y_407_, v___x_445_);
v___x_447_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_447_);
v___x_449_ = v___x_413_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_456_, v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_474_ = l_Lean_Name_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_492_; 
v___x_490_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_478_, v_a_486_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_n(v_a_491_, 2);
lean_dec_ref(v___x_490_);
v___x_492_ = l_Lean_Meta_Grind_simpCore(v_a_491_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_expr_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v___x_492_);
v_expr_494_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_expr_494_);
v___x_495_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_494_, v_a_486_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = l_Lean_Meta_Sym_unfoldReducible(v_a_496_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
v___x_499_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_498_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_500_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_502_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = l_Lean_Meta_Grind_foldProjs(v_a_504_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_Meta_Sym_normalizeLevels(v_a_506_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_508_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc_n(v_a_510_, 2);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_493_, v_a_510_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_expr_513_; lean_object* v___x_514_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v_expr_513_ = lean_ctor_get(v_a_510_, 0);
lean_inc_ref(v_expr_513_);
lean_dec(v_a_510_);
v___x_514_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_513_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_n(v_a_515_, 2);
lean_dec_ref(v___x_514_);
v___x_516_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_512_, v_a_515_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v_expr_518_; lean_object* v___x_519_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v___x_516_);
v_expr_518_ = lean_ctor_get(v_a_515_, 0);
lean_inc_ref(v_expr_518_);
lean_dec(v_a_515_);
v___x_519_ = l_Lean_Meta_Sym_canon(v_expr_518_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_520_, v_a_484_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_569_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_569_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_569_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_569_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_options_540_; uint8_t v_hasTrace_541_; 
v_options_540_ = lean_ctor_get(v_a_487_, 2);
v_hasTrace_541_ = lean_ctor_get_uint8(v_options_540_, sizeof(void*)*1);
if (v_hasTrace_541_ == 0)
{
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
goto v___jp_526_;
}
else
{
lean_object* v_inheritedTraceOptions_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_inheritedTraceOptions_542_ = lean_ctor_get(v_a_487_, 13);
v___x_543_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_542_, v_options_540_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
goto v___jp_526_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_updateLastTag(v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec_ref(v___x_546_);
v___x_547_ = l_Lean_MessageData_ofExpr(v_a_491_);
v___x_548_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_inc(v_a_522_);
v___x_550_ = l_Lean_MessageData_ofExpr(v_a_522_);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_543_, v___x_551_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_dec_ref(v___x_552_);
goto v___jp_526_;
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_del_object(v___x_524_);
lean_dec(v_a_522_);
lean_dec(v_a_517_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_524_);
lean_dec(v_a_522_);
lean_dec(v_a_517_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
v_a_561_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_546_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_546_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
v___jp_526_:
{
lean_object* v_proof_x3f_527_; uint8_t v_cache_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_538_; 
v_proof_x3f_527_ = lean_ctor_get(v_a_517_, 1);
v_cache_528_ = lean_ctor_get_uint8(v_a_517_, sizeof(void*)*2);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_517_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_a_517_, 0);
lean_dec(v_unused_539_);
v___x_530_ = v_a_517_;
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_proof_x3f_527_);
lean_dec(v_a_517_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v_a_522_);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_522_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_proof_x3f_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_537_, sizeof(void*)*2, v_cache_528_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_533_);
v___x_535_ = v___x_524_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_517_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_570_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_521_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_521_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_517_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_578_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_519_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_519_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_dec(v_a_515_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
return v___x_516_;
}
}
else
{
lean_dec(v_a_512_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
return v___x_514_;
}
}
else
{
lean_dec(v_a_510_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
return v___x_511_;
}
}
else
{
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
return v___x_509_;
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_586_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_507_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_507_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_594_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_505_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_505_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_602_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_503_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_503_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_610_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_501_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_501_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_618_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_499_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_499_);
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
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_493_);
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
v_a_626_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_497_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_497_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec(v_a_491_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = lean_grind_preprocess(v_e_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_647_, lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_647_, v_msg_648_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_661_, lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_661_, v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
return v_res_674_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_682_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_683_ = l_Lean_Name_append(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_696_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_697_ = l_Lean_mkConst(v___x_696_, v___x_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_698_, lean_object* v_proof_699_, lean_object* v_generation_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_a_705_);
lean_inc(v_a_704_);
lean_inc_ref(v_a_703_);
lean_inc(v_a_702_);
lean_inc(v_a_701_);
lean_inc_ref(v_prop_698_);
v___x_712_ = lean_grind_preprocess(v_prop_698_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_781_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_781_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_781_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_781_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_expr_717_; lean_object* v_proof_x3f_718_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_765_; 
v_expr_717_ = lean_ctor_get(v_a_713_, 0);
lean_inc_ref(v_expr_717_);
v_proof_x3f_718_ = lean_ctor_get(v_a_713_, 1);
lean_inc(v_proof_x3f_718_);
lean_dec(v_a_713_);
if (lean_obj_tag(v_proof_x3f_718_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_val_778_ = lean_ctor_get(v_proof_x3f_718_, 0);
lean_inc(v_val_778_);
lean_dec_ref(v_proof_x3f_718_);
v___x_779_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_717_);
lean_inc_ref(v_prop_698_);
v___x_780_ = l_Lean_mkApp4(v___x_779_, v_prop_698_, v_expr_717_, v_val_778_, v_proof_699_);
v___y_765_ = v___x_780_;
goto v___jp_764_;
}
else
{
lean_dec(v_proof_x3f_718_);
v___y_765_ = v_proof_699_;
goto v___jp_764_;
}
v___jp_719_:
{
lean_object* v___x_722_; lean_object* v_toGoalState_723_; lean_object* v_mvarId_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_763_; 
v___x_722_ = lean_st_ref_take(v___y_721_);
v_toGoalState_723_ = lean_ctor_get(v___x_722_, 0);
v_mvarId_724_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_763_ == 0)
{
v___x_726_ = v___x_722_;
v_isShared_727_ = v_isSharedCheck_763_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_mvarId_724_);
lean_inc(v_toGoalState_723_);
lean_dec(v___x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_763_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_nextDeclIdx_728_; lean_object* v_enodeMap_729_; lean_object* v_exprs_730_; lean_object* v_parents_731_; lean_object* v_congrTable_732_; lean_object* v_appMap_733_; lean_object* v_indicesFound_734_; lean_object* v_newFacts_735_; uint8_t v_inconsistent_736_; lean_object* v_nextIdx_737_; lean_object* v_newRawFacts_738_; lean_object* v_facts_739_; lean_object* v_extThms_740_; lean_object* v_ematch_741_; lean_object* v_inj_742_; lean_object* v_split_743_; lean_object* v_clean_744_; lean_object* v_sstates_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_762_; 
v_nextDeclIdx_728_ = lean_ctor_get(v_toGoalState_723_, 0);
v_enodeMap_729_ = lean_ctor_get(v_toGoalState_723_, 1);
v_exprs_730_ = lean_ctor_get(v_toGoalState_723_, 2);
v_parents_731_ = lean_ctor_get(v_toGoalState_723_, 3);
v_congrTable_732_ = lean_ctor_get(v_toGoalState_723_, 4);
v_appMap_733_ = lean_ctor_get(v_toGoalState_723_, 5);
v_indicesFound_734_ = lean_ctor_get(v_toGoalState_723_, 6);
v_newFacts_735_ = lean_ctor_get(v_toGoalState_723_, 7);
v_inconsistent_736_ = lean_ctor_get_uint8(v_toGoalState_723_, sizeof(void*)*17);
v_nextIdx_737_ = lean_ctor_get(v_toGoalState_723_, 8);
v_newRawFacts_738_ = lean_ctor_get(v_toGoalState_723_, 9);
v_facts_739_ = lean_ctor_get(v_toGoalState_723_, 10);
v_extThms_740_ = lean_ctor_get(v_toGoalState_723_, 11);
v_ematch_741_ = lean_ctor_get(v_toGoalState_723_, 12);
v_inj_742_ = lean_ctor_get(v_toGoalState_723_, 13);
v_split_743_ = lean_ctor_get(v_toGoalState_723_, 14);
v_clean_744_ = lean_ctor_get(v_toGoalState_723_, 15);
v_sstates_745_ = lean_ctor_get(v_toGoalState_723_, 16);
v_isSharedCheck_762_ = !lean_is_exclusive(v_toGoalState_723_);
if (v_isSharedCheck_762_ == 0)
{
v___x_747_ = v_toGoalState_723_;
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_sstates_745_);
lean_inc(v_clean_744_);
lean_inc(v_split_743_);
lean_inc(v_inj_742_);
lean_inc(v_ematch_741_);
lean_inc(v_extThms_740_);
lean_inc(v_facts_739_);
lean_inc(v_newRawFacts_738_);
lean_inc(v_nextIdx_737_);
lean_inc(v_newFacts_735_);
lean_inc(v_indicesFound_734_);
lean_inc(v_appMap_733_);
lean_inc(v_congrTable_732_);
lean_inc(v_parents_731_);
lean_inc(v_exprs_730_);
lean_inc(v_enodeMap_729_);
lean_inc(v_nextDeclIdx_728_);
lean_dec(v_toGoalState_723_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v_expr_717_);
lean_ctor_set(v___x_749_, 1, v___y_720_);
lean_ctor_set(v___x_749_, 2, v_generation_700_);
v___x_750_ = lean_array_push(v_newFacts_735_, v___x_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 7, v___x_750_);
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_nextDeclIdx_728_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_enodeMap_729_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_exprs_730_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_parents_731_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_congrTable_732_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v_appMap_733_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_indicesFound_734_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_nextIdx_737_);
lean_ctor_set(v_reuseFailAlloc_761_, 9, v_newRawFacts_738_);
lean_ctor_set(v_reuseFailAlloc_761_, 10, v_facts_739_);
lean_ctor_set(v_reuseFailAlloc_761_, 11, v_extThms_740_);
lean_ctor_set(v_reuseFailAlloc_761_, 12, v_ematch_741_);
lean_ctor_set(v_reuseFailAlloc_761_, 13, v_inj_742_);
lean_ctor_set(v_reuseFailAlloc_761_, 14, v_split_743_);
lean_ctor_set(v_reuseFailAlloc_761_, 15, v_clean_744_);
lean_ctor_set(v_reuseFailAlloc_761_, 16, v_sstates_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_761_, sizeof(void*)*17, v_inconsistent_736_);
v___x_752_ = v_reuseFailAlloc_761_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_752_);
v___x_754_ = v___x_726_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_mvarId_724_);
v___x_754_ = v_reuseFailAlloc_760_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_st_ref_set(v___y_721_, v___x_754_);
v___x_756_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_756_);
v___x_758_ = v___x_715_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
v___jp_764_:
{
lean_object* v_options_766_; uint8_t v_hasTrace_767_; 
v_options_766_ = lean_ctor_get(v_a_709_, 2);
v_hasTrace_767_ = lean_ctor_get_uint8(v_options_766_, sizeof(void*)*1);
if (v_hasTrace_767_ == 0)
{
lean_dec_ref(v_prop_698_);
v___y_720_ = v___y_765_;
v___y_721_ = v_a_701_;
goto v___jp_719_;
}
else
{
lean_object* v_inheritedTraceOptions_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_inheritedTraceOptions_768_ = lean_ctor_get(v_a_709_, 13);
v___x_769_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_770_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_768_, v_options_766_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec_ref(v_prop_698_);
v___y_720_ = v___y_765_;
v___y_721_ = v_a_701_;
goto v___jp_719_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_772_ = l_Lean_MessageData_ofExpr(v_prop_698_);
v___x_773_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
lean_inc_ref(v_expr_717_);
v___x_775_ = l_Lean_MessageData_ofExpr(v_expr_717_);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_769_, v___x_776_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref(v___x_777_);
v___y_720_ = v___y_765_;
v___y_721_ = v_a_701_;
goto v___jp_719_;
}
else
{
lean_dec_ref(v___y_765_);
lean_dec_ref(v_expr_717_);
lean_del_object(v___x_715_);
lean_dec(v_generation_700_);
return v___x_777_;
}
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_generation_700_);
lean_dec_ref(v_proof_699_);
lean_dec_ref(v_prop_698_);
v_a_782_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_712_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_712_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_790_, lean_object* v_proof_791_, lean_object* v_generation_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_790_, v_proof_791_, v_generation_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec(v_a_793_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_805_, lean_object* v_generation_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; 
lean_inc(v_a_816_);
lean_inc_ref(v_a_815_);
lean_inc(v_a_814_);
lean_inc_ref(v_a_813_);
lean_inc_ref(v_proof_805_);
v___x_818_ = lean_infer_type(v_proof_805_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_options_819_; uint8_t v_hasTrace_820_; 
v_options_819_ = lean_ctor_get(v_a_815_, 2);
v_hasTrace_820_ = lean_ctor_get_uint8(v_options_819_, sizeof(void*)*1);
if (v_hasTrace_820_ == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_818_);
v___x_822_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_821_, v_proof_805_, v_generation_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v_inheritedTraceOptions_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_a_823_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_818_);
v_inheritedTraceOptions_824_ = lean_ctor_get(v_a_815_, 13);
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_826_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_824_, v_options_819_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_823_, v_proof_805_, v_generation_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc(v_a_823_);
v___x_829_ = l_Lean_MessageData_ofExpr(v_a_823_);
v___x_830_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_825_, v___x_829_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; 
lean_dec_ref(v___x_830_);
v___x_831_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_823_, v_proof_805_, v_generation_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
return v___x_831_;
}
else
{
lean_dec(v_a_823_);
lean_dec(v_generation_806_);
lean_dec_ref(v_proof_805_);
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_generation_806_);
lean_dec_ref(v_proof_805_);
v_a_832_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_840_, lean_object* v_generation_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_Grind_pushNewFact(v_proof_840_, v_generation_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec(v_a_842_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; 
v___x_865_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_854_, v_a_861_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = l_Lean_Meta_Sym_unfoldReducible(v_a_866_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_868_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_870_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = l_Lean_Meta_Grind_foldProjs(v_a_872_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = l_Lean_Meta_Sym_normalizeLevels(v_a_874_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = l_Lean_Meta_Sym_canon(v_a_876_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_878_, v_a_859_);
return v___x_879_;
}
else
{
return v___x_877_;
}
}
else
{
return v___x_875_;
}
}
else
{
return v___x_873_;
}
}
else
{
return v___x_871_;
}
}
else
{
return v___x_869_;
}
}
else
{
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_892_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_Grind_preprocessLight(v_e_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
return v_res_917_;
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

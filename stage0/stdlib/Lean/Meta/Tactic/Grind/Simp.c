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
lean_object* v___x_109_; lean_object* v_congrThms_110_; lean_object* v_simp_111_; lean_object* v_lastTag_112_; lean_object* v_counters_113_; lean_object* v_splitDiags_114_; lean_object* v_ematchDiags_115_; lean_object* v_lawfulEqCmpMap_116_; lean_object* v_reflCmpMap_117_; lean_object* v_anchors_118_; lean_object* v_instanceMap_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_168_; 
v___x_109_ = lean_st_ref_take(v___y_101_);
v_congrThms_110_ = lean_ctor_get(v___x_109_, 0);
v_simp_111_ = lean_ctor_get(v___x_109_, 1);
v_lastTag_112_ = lean_ctor_get(v___x_109_, 2);
v_counters_113_ = lean_ctor_get(v___x_109_, 3);
v_splitDiags_114_ = lean_ctor_get(v___x_109_, 4);
v_ematchDiags_115_ = lean_ctor_get(v___x_109_, 5);
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
lean_inc(v_ematchDiags_115_);
lean_inc(v_splitDiags_114_);
lean_inc(v_counters_113_);
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
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_counters_113_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_splitDiags_114_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_ematchDiags_115_);
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
v_simpMethods_128_ = lean_ctor_get(v___y_100_, 1);
lean_inc_ref(v_simpMethods_128_);
lean_inc_ref(v_simp_127_);
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
lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v___x_136_; lean_object* v_congrThms_137_; lean_object* v_lastTag_138_; lean_object* v_counters_139_; lean_object* v_splitDiags_140_; lean_object* v_ematchDiags_141_; lean_object* v_lawfulEqCmpMap_142_; lean_object* v_reflCmpMap_143_; lean_object* v_anchors_144_; lean_object* v_instanceMap_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_156_; 
v_fst_134_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_fst_134_);
v_snd_135_ = lean_ctor_get(v_a_130_, 1);
lean_inc(v_snd_135_);
lean_dec(v_a_130_);
v___x_136_ = lean_st_ref_take(v___y_101_);
v_congrThms_137_ = lean_ctor_get(v___x_136_, 0);
v_lastTag_138_ = lean_ctor_get(v___x_136_, 2);
v_counters_139_ = lean_ctor_get(v___x_136_, 3);
v_splitDiags_140_ = lean_ctor_get(v___x_136_, 4);
v_ematchDiags_141_ = lean_ctor_get(v___x_136_, 5);
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
lean_inc(v_ematchDiags_141_);
lean_inc(v_splitDiags_140_);
lean_inc(v_counters_139_);
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
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_counters_139_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_splitDiags_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 5, v_ematchDiags_141_);
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
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_options_193_; lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_options_193_ = lean_ctor_get(v_a_190_, 2);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_194_, 0, v_e_182_);
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_simpCore___closed__0));
v___x_196_ = lean_box(0);
v___x_197_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_195_, v_options_193_, v___f_194_, v___x_196_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Grind_simpCore(v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* v_e_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_congrThms_222_; lean_object* v_simp_223_; lean_object* v_lastTag_224_; lean_object* v_counters_225_; lean_object* v_splitDiags_226_; lean_object* v_ematchDiags_227_; lean_object* v_lawfulEqCmpMap_228_; lean_object* v_reflCmpMap_229_; lean_object* v_anchors_230_; lean_object* v_instanceMap_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_282_; 
v___x_221_ = lean_st_ref_take(v___y_213_);
v_congrThms_222_ = lean_ctor_get(v___x_221_, 0);
v_simp_223_ = lean_ctor_get(v___x_221_, 1);
v_lastTag_224_ = lean_ctor_get(v___x_221_, 2);
v_counters_225_ = lean_ctor_get(v___x_221_, 3);
v_splitDiags_226_ = lean_ctor_get(v___x_221_, 4);
v_ematchDiags_227_ = lean_ctor_get(v___x_221_, 5);
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
lean_inc(v_ematchDiags_227_);
lean_inc(v_splitDiags_226_);
lean_inc(v_counters_225_);
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
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_counters_225_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_splitDiags_226_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_ematchDiags_227_);
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
v_simpMethods_242_ = lean_ctor_get(v___y_212_, 1);
lean_inc_ref(v_simpMethods_242_);
lean_inc_ref(v_simp_241_);
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
lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_250_; lean_object* v_congrThms_251_; lean_object* v_lastTag_252_; lean_object* v_counters_253_; lean_object* v_splitDiags_254_; lean_object* v_ematchDiags_255_; lean_object* v_lawfulEqCmpMap_256_; lean_object* v_reflCmpMap_257_; lean_object* v_anchors_258_; lean_object* v_instanceMap_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_fst_248_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_fst_248_);
v_snd_249_ = lean_ctor_get(v_a_244_, 1);
lean_inc(v_snd_249_);
lean_dec(v_a_244_);
v___x_250_ = lean_st_ref_take(v___y_213_);
v_congrThms_251_ = lean_ctor_get(v___x_250_, 0);
v_lastTag_252_ = lean_ctor_get(v___x_250_, 2);
v_counters_253_ = lean_ctor_get(v___x_250_, 3);
v_splitDiags_254_ = lean_ctor_get(v___x_250_, 4);
v_ematchDiags_255_ = lean_ctor_get(v___x_250_, 5);
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
lean_inc(v_ematchDiags_255_);
lean_inc(v_splitDiags_254_);
lean_inc(v_counters_253_);
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
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_counters_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_splitDiags_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_ematchDiags_255_);
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
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_options_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_options_307_ = lean_ctor_get(v_a_304_, 2);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_308_, 0, v_e_296_);
v___x_309_ = ((lean_object*)(l_Lean_Meta_Grind_dsimpCore___closed__0));
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_309_, v_options_307_, v___f_308_, v___x_310_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_dsimpCore(v_e_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_env_386_; lean_object* v___x_387_; lean_object* v_mctx_388_; lean_object* v_lctx_389_; lean_object* v_options_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_env_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_385_);
v___x_387_ = lean_st_ref_get(v___y_381_);
v_mctx_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_mctx_388_);
lean_dec(v___x_387_);
v_lctx_389_ = lean_ctor_get(v___y_380_, 2);
v_options_390_ = lean_ctor_get(v___y_382_, 2);
lean_inc_ref(v_options_390_);
lean_inc_ref(v_lctx_389_);
v___x_391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_391_, 0, v_env_386_);
lean_ctor_set(v___x_391_, 1, v_mctx_388_);
lean_ctor_set(v___x_391_, 2, v_lctx_389_);
lean_ctor_set(v___x_391_, 3, v_options_390_);
v___x_392_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_msgData_379_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_401_; double v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_float_of_nat(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_406_, lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_ref_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_459_; 
v_ref_413_ = lean_ctor_get(v___y_410_, 5);
v___x_414_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_459_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v_traceState_420_; lean_object* v_env_421_; lean_object* v_nextMacroScope_422_; lean_object* v_ngen_423_; lean_object* v_auxDeclNGen_424_; lean_object* v_cache_425_; lean_object* v_messages_426_; lean_object* v_infoState_427_; lean_object* v_snapshotTasks_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_458_; 
v___x_419_ = lean_st_ref_take(v___y_411_);
v_traceState_420_ = lean_ctor_get(v___x_419_, 4);
v_env_421_ = lean_ctor_get(v___x_419_, 0);
v_nextMacroScope_422_ = lean_ctor_get(v___x_419_, 1);
v_ngen_423_ = lean_ctor_get(v___x_419_, 2);
v_auxDeclNGen_424_ = lean_ctor_get(v___x_419_, 3);
v_cache_425_ = lean_ctor_get(v___x_419_, 5);
v_messages_426_ = lean_ctor_get(v___x_419_, 6);
v_infoState_427_ = lean_ctor_get(v___x_419_, 7);
v_snapshotTasks_428_ = lean_ctor_get(v___x_419_, 8);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_458_ == 0)
{
v___x_430_ = v___x_419_;
v_isShared_431_ = v_isSharedCheck_458_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snapshotTasks_428_);
lean_inc(v_infoState_427_);
lean_inc(v_messages_426_);
lean_inc(v_cache_425_);
lean_inc(v_traceState_420_);
lean_inc(v_auxDeclNGen_424_);
lean_inc(v_ngen_423_);
lean_inc(v_nextMacroScope_422_);
lean_inc(v_env_421_);
lean_dec(v___x_419_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_458_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint64_t v_tid_432_; lean_object* v_traces_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_457_; 
v_tid_432_ = lean_ctor_get_uint64(v_traceState_420_, sizeof(void*)*1);
v_traces_433_ = lean_ctor_get(v_traceState_420_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_traceState_420_);
if (v_isSharedCheck_457_ == 0)
{
v___x_435_ = v_traceState_420_;
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_traces_433_);
lean_dec(v_traceState_420_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; double v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_439_ = 0;
v___x_440_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_441_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_441_, 0, v_cls_406_);
lean_ctor_set(v___x_441_, 1, v___x_437_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
lean_ctor_set_float(v___x_441_, sizeof(void*)*3, v___x_438_);
lean_ctor_set_float(v___x_441_, sizeof(void*)*3 + 8, v___x_438_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*3 + 16, v___x_439_);
v___x_442_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_443_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v_a_415_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_inc(v_ref_413_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_ref_413_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_PersistentArray_push___redArg(v_traces_433_, v___x_444_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_445_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_445_);
lean_ctor_set_uint64(v_reuseFailAlloc_456_, sizeof(void*)*1, v_tid_432_);
v___x_447_ = v_reuseFailAlloc_456_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v___x_447_);
v___x_449_ = v___x_430_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_nextMacroScope_422_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_ngen_423_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_auxDeclNGen_424_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v_cache_425_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_messages_426_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_infoState_427_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_snapshotTasks_428_);
v___x_449_ = v_reuseFailAlloc_455_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = lean_st_ref_set(v___y_411_, v___x_449_);
v___x_451_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_451_);
v___x_453_ = v___x_417_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_460_, v_msg_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_478_ = l_Lean_Name_append(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; lean_object* v_a_495_; lean_object* v___x_496_; 
v___x_494_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_482_, v_a_490_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc_n(v_a_495_, 2);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_Meta_Grind_simpCore(v_a_495_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_expr_498_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v_expr_498_ = lean_ctor_get(v_a_497_, 0);
lean_inc_ref(v_expr_498_);
v___x_499_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_498_, v_a_490_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = l_Lean_Meta_Sym_unfoldReducible(v_a_500_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_502_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_504_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_506_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_Meta_Grind_foldProjs(v_a_508_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = l_Lean_Meta_Sym_normalizeLevels(v_a_510_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_512_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_n(v_a_514_, 2);
lean_dec_ref(v___x_513_);
v___x_515_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_497_, v_a_514_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_expr_517_; lean_object* v___x_518_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v_expr_517_ = lean_ctor_get(v_a_514_, 0);
lean_inc_ref(v_expr_517_);
lean_dec(v_a_514_);
v___x_518_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_517_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc_n(v_a_519_, 2);
lean_dec_ref(v___x_518_);
v___x_520_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_516_, v_a_519_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_expr_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v_expr_522_ = lean_ctor_get(v_a_519_, 0);
lean_inc_ref(v_expr_522_);
lean_dec(v_a_519_);
v___x_523_ = l_Lean_Meta_Sym_canon(v_expr_522_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_524_, v_a_488_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_573_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_573_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_573_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_573_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_options_544_; uint8_t v_hasTrace_545_; 
v_options_544_ = lean_ctor_get(v_a_491_, 2);
v_hasTrace_545_ = lean_ctor_get_uint8(v_options_544_, sizeof(void*)*1);
if (v_hasTrace_545_ == 0)
{
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
goto v___jp_530_;
}
else
{
lean_object* v_inheritedTraceOptions_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_inheritedTraceOptions_546_ = lean_ctor_get(v_a_491_, 13);
v___x_547_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_548_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_546_, v_options_544_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
goto v___jp_530_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Grind_updateLastTag(v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___x_550_);
v___x_551_ = l_Lean_MessageData_ofExpr(v_a_495_);
v___x_552_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_inc(v_a_526_);
v___x_554_ = l_Lean_MessageData_ofExpr(v_a_526_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_547_, v___x_555_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec_ref(v___x_556_);
goto v___jp_530_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_del_object(v___x_528_);
lean_dec(v_a_526_);
lean_dec(v_a_521_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_528_);
lean_dec(v_a_526_);
lean_dec(v_a_521_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
v_a_565_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_550_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_550_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
v___jp_530_:
{
lean_object* v_proof_x3f_531_; uint8_t v_cache_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_542_; 
v_proof_x3f_531_ = lean_ctor_get(v_a_521_, 1);
v_cache_532_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_a_521_, 0);
lean_dec(v_unused_543_);
v___x_534_ = v_a_521_;
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_proof_x3f_531_);
lean_dec(v_a_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_a_526_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_526_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_proof_x3f_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_541_, sizeof(void*)*2, v_cache_532_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_537_);
v___x_539_ = v___x_528_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_a_521_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_574_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_525_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_525_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
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
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_521_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_582_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_523_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_523_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_dec(v_a_519_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
return v___x_520_;
}
}
else
{
lean_dec(v_a_516_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
return v___x_518_;
}
}
else
{
lean_dec(v_a_514_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
return v___x_515_;
}
}
else
{
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
return v___x_513_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_590_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_511_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_511_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_598_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_509_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_509_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_606_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_507_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_507_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_614_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_505_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_505_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_622_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_503_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_503_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_497_);
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
v_a_630_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_501_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_501_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
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
lean_dec(v_a_495_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec(v_a_483_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = lean_grind_preprocess(v_e_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_651_, v_msg_652_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec(v___y_667_);
return v_res_678_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_686_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_687_ = l_Lean_Name_append(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_700_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_701_ = l_Lean_mkConst(v___x_700_, v___x_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_702_, lean_object* v_proof_703_, lean_object* v_generation_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc(v_a_714_);
lean_inc_ref(v_a_713_);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc(v_a_705_);
lean_inc_ref(v_prop_702_);
v___x_716_ = lean_grind_preprocess(v_prop_702_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_785_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_785_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_785_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_785_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_expr_721_; lean_object* v_proof_x3f_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_769_; 
v_expr_721_ = lean_ctor_get(v_a_717_, 0);
lean_inc_ref(v_expr_721_);
v_proof_x3f_722_ = lean_ctor_get(v_a_717_, 1);
lean_inc(v_proof_x3f_722_);
lean_dec(v_a_717_);
if (lean_obj_tag(v_proof_x3f_722_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_val_782_ = lean_ctor_get(v_proof_x3f_722_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v_proof_x3f_722_);
v___x_783_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_721_);
lean_inc_ref(v_prop_702_);
v___x_784_ = l_Lean_mkApp4(v___x_783_, v_prop_702_, v_expr_721_, v_val_782_, v_proof_703_);
v___y_769_ = v___x_784_;
goto v___jp_768_;
}
else
{
lean_dec(v_proof_x3f_722_);
v___y_769_ = v_proof_703_;
goto v___jp_768_;
}
v___jp_723_:
{
lean_object* v___x_726_; lean_object* v_toGoalState_727_; lean_object* v_mvarId_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_767_; 
v___x_726_ = lean_st_ref_take(v___y_725_);
v_toGoalState_727_ = lean_ctor_get(v___x_726_, 0);
v_mvarId_728_ = lean_ctor_get(v___x_726_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_767_ == 0)
{
v___x_730_ = v___x_726_;
v_isShared_731_ = v_isSharedCheck_767_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_mvarId_728_);
lean_inc(v_toGoalState_727_);
lean_dec(v___x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_767_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_nextDeclIdx_732_; lean_object* v_enodeMap_733_; lean_object* v_exprs_734_; lean_object* v_parents_735_; lean_object* v_congrTable_736_; lean_object* v_appMap_737_; lean_object* v_indicesFound_738_; lean_object* v_newFacts_739_; uint8_t v_inconsistent_740_; lean_object* v_nextIdx_741_; lean_object* v_newRawFacts_742_; lean_object* v_facts_743_; lean_object* v_extThms_744_; lean_object* v_ematch_745_; lean_object* v_inj_746_; lean_object* v_split_747_; lean_object* v_clean_748_; lean_object* v_sstates_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_766_; 
v_nextDeclIdx_732_ = lean_ctor_get(v_toGoalState_727_, 0);
v_enodeMap_733_ = lean_ctor_get(v_toGoalState_727_, 1);
v_exprs_734_ = lean_ctor_get(v_toGoalState_727_, 2);
v_parents_735_ = lean_ctor_get(v_toGoalState_727_, 3);
v_congrTable_736_ = lean_ctor_get(v_toGoalState_727_, 4);
v_appMap_737_ = lean_ctor_get(v_toGoalState_727_, 5);
v_indicesFound_738_ = lean_ctor_get(v_toGoalState_727_, 6);
v_newFacts_739_ = lean_ctor_get(v_toGoalState_727_, 7);
v_inconsistent_740_ = lean_ctor_get_uint8(v_toGoalState_727_, sizeof(void*)*17);
v_nextIdx_741_ = lean_ctor_get(v_toGoalState_727_, 8);
v_newRawFacts_742_ = lean_ctor_get(v_toGoalState_727_, 9);
v_facts_743_ = lean_ctor_get(v_toGoalState_727_, 10);
v_extThms_744_ = lean_ctor_get(v_toGoalState_727_, 11);
v_ematch_745_ = lean_ctor_get(v_toGoalState_727_, 12);
v_inj_746_ = lean_ctor_get(v_toGoalState_727_, 13);
v_split_747_ = lean_ctor_get(v_toGoalState_727_, 14);
v_clean_748_ = lean_ctor_get(v_toGoalState_727_, 15);
v_sstates_749_ = lean_ctor_get(v_toGoalState_727_, 16);
v_isSharedCheck_766_ = !lean_is_exclusive(v_toGoalState_727_);
if (v_isSharedCheck_766_ == 0)
{
v___x_751_ = v_toGoalState_727_;
v_isShared_752_ = v_isSharedCheck_766_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_sstates_749_);
lean_inc(v_clean_748_);
lean_inc(v_split_747_);
lean_inc(v_inj_746_);
lean_inc(v_ematch_745_);
lean_inc(v_extThms_744_);
lean_inc(v_facts_743_);
lean_inc(v_newRawFacts_742_);
lean_inc(v_nextIdx_741_);
lean_inc(v_newFacts_739_);
lean_inc(v_indicesFound_738_);
lean_inc(v_appMap_737_);
lean_inc(v_congrTable_736_);
lean_inc(v_parents_735_);
lean_inc(v_exprs_734_);
lean_inc(v_enodeMap_733_);
lean_inc(v_nextDeclIdx_732_);
lean_dec(v_toGoalState_727_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_766_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v_expr_721_);
lean_ctor_set(v___x_753_, 1, v___y_724_);
lean_ctor_set(v___x_753_, 2, v_generation_704_);
v___x_754_ = lean_array_push(v_newFacts_739_, v___x_753_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 7, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_nextDeclIdx_732_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_enodeMap_733_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_exprs_734_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_parents_735_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_congrTable_736_);
lean_ctor_set(v_reuseFailAlloc_765_, 5, v_appMap_737_);
lean_ctor_set(v_reuseFailAlloc_765_, 6, v_indicesFound_738_);
lean_ctor_set(v_reuseFailAlloc_765_, 7, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_765_, 8, v_nextIdx_741_);
lean_ctor_set(v_reuseFailAlloc_765_, 9, v_newRawFacts_742_);
lean_ctor_set(v_reuseFailAlloc_765_, 10, v_facts_743_);
lean_ctor_set(v_reuseFailAlloc_765_, 11, v_extThms_744_);
lean_ctor_set(v_reuseFailAlloc_765_, 12, v_ematch_745_);
lean_ctor_set(v_reuseFailAlloc_765_, 13, v_inj_746_);
lean_ctor_set(v_reuseFailAlloc_765_, 14, v_split_747_);
lean_ctor_set(v_reuseFailAlloc_765_, 15, v_clean_748_);
lean_ctor_set(v_reuseFailAlloc_765_, 16, v_sstates_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*17, v_inconsistent_740_);
v___x_756_ = v_reuseFailAlloc_765_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_756_);
v___x_758_ = v___x_730_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_mvarId_728_);
v___x_758_ = v_reuseFailAlloc_764_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = lean_st_ref_set(v___y_725_, v___x_758_);
v___x_760_ = lean_box(0);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_760_);
v___x_762_ = v___x_719_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
v___jp_768_:
{
lean_object* v_options_770_; uint8_t v_hasTrace_771_; 
v_options_770_ = lean_ctor_get(v_a_713_, 2);
v_hasTrace_771_ = lean_ctor_get_uint8(v_options_770_, sizeof(void*)*1);
if (v_hasTrace_771_ == 0)
{
lean_dec_ref(v_prop_702_);
v___y_724_ = v___y_769_;
v___y_725_ = v_a_705_;
goto v___jp_723_;
}
else
{
lean_object* v_inheritedTraceOptions_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_inheritedTraceOptions_772_ = lean_ctor_get(v_a_713_, 13);
v___x_773_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_774_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_772_, v_options_770_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_prop_702_);
v___y_724_ = v___y_769_;
v___y_725_ = v_a_705_;
goto v___jp_723_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_776_ = l_Lean_MessageData_ofExpr(v_prop_702_);
v___x_777_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
lean_inc_ref(v_expr_721_);
v___x_779_ = l_Lean_MessageData_ofExpr(v_expr_721_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_773_, v___x_780_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_dec_ref(v___x_781_);
v___y_724_ = v___y_769_;
v___y_725_ = v_a_705_;
goto v___jp_723_;
}
else
{
lean_dec_ref(v___y_769_);
lean_dec_ref(v_expr_721_);
lean_del_object(v___x_719_);
lean_dec(v_generation_704_);
return v___x_781_;
}
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_generation_704_);
lean_dec_ref(v_proof_703_);
lean_dec_ref(v_prop_702_);
v_a_786_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_716_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_716_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_794_, lean_object* v_proof_795_, lean_object* v_generation_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_794_, v_proof_795_, v_generation_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec(v_a_797_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_809_, lean_object* v_generation_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
lean_inc(v_a_820_);
lean_inc_ref(v_a_819_);
lean_inc(v_a_818_);
lean_inc_ref(v_a_817_);
lean_inc_ref(v_proof_809_);
v___x_822_ = lean_infer_type(v_proof_809_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_options_823_; uint8_t v_hasTrace_824_; 
v_options_823_ = lean_ctor_get(v_a_819_, 2);
v_hasTrace_824_ = lean_ctor_get_uint8(v_options_823_, sizeof(void*)*1);
if (v_hasTrace_824_ == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_825_);
lean_dec_ref(v___x_822_);
v___x_826_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_825_, v_proof_809_, v_generation_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_826_;
}
else
{
lean_object* v_a_827_; lean_object* v_inheritedTraceOptions_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_a_827_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_822_);
v_inheritedTraceOptions_828_ = lean_ctor_get(v_a_819_, 13);
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_830_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_828_, v_options_823_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_827_, v_proof_809_, v_generation_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_inc(v_a_827_);
v___x_833_ = l_Lean_MessageData_ofExpr(v_a_827_);
v___x_834_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_829_, v___x_833_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v___x_834_);
v___x_835_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_827_, v_proof_809_, v_generation_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_835_;
}
else
{
lean_dec(v_a_827_);
lean_dec(v_generation_810_);
lean_dec_ref(v_proof_809_);
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_generation_810_);
lean_dec_ref(v_proof_809_);
v_a_836_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_822_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_822_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_844_, lean_object* v_generation_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Grind_pushNewFact(v_proof_844_, v_generation_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec(v_a_846_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_871_; 
v___x_869_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_858_, v_a_865_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
v___x_871_ = l_Lean_Meta_Sym_unfoldReducible(v_a_870_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_872_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_874_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = l_Lean_Meta_Grind_foldProjs(v_a_876_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = l_Lean_Meta_Sym_normalizeLevels(v_a_878_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = l_Lean_Meta_Sym_canon(v_a_880_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v___x_883_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_882_, v_a_863_);
return v___x_883_;
}
else
{
return v___x_881_;
}
}
else
{
return v___x_879_;
}
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_896_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_Grind_preprocessLight(v_e_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec(v_a_910_);
return v_res_921_;
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

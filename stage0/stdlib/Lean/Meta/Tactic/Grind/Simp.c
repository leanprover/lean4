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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_126_ = lean_st_ref_put(v___y_101_, v___x_125_);
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
v___x_151_ = lean_st_ref_put(v___y_101_, v___x_150_);
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
lean_object* v_toCold_193_; lean_object* v_options_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_toCold_193_ = lean_ctor_get(v_a_190_, 0);
v_options_194_ = lean_ctor_get(v_toCold_193_, 2);
v___f_195_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_195_, 0, v_e_182_);
v___x_196_ = ((lean_object*)(l_Lean_Meta_Grind_simpCore___closed__0));
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_196_, v_options_194_, v___f_195_, v___x_197_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_Grind_simpCore(v_e_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* v_e_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_congrThms_223_; lean_object* v_simp_224_; lean_object* v_lastTag_225_; lean_object* v_counters_226_; lean_object* v_splitDiags_227_; lean_object* v_ematchDiags_228_; lean_object* v_lawfulEqCmpMap_229_; lean_object* v_reflCmpMap_230_; lean_object* v_anchors_231_; lean_object* v_instanceMap_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_283_; 
v___x_222_ = lean_st_ref_take(v___y_214_);
v_congrThms_223_ = lean_ctor_get(v___x_222_, 0);
v_simp_224_ = lean_ctor_get(v___x_222_, 1);
v_lastTag_225_ = lean_ctor_get(v___x_222_, 2);
v_counters_226_ = lean_ctor_get(v___x_222_, 3);
v_splitDiags_227_ = lean_ctor_get(v___x_222_, 4);
v_ematchDiags_228_ = lean_ctor_get(v___x_222_, 5);
v_lawfulEqCmpMap_229_ = lean_ctor_get(v___x_222_, 6);
v_reflCmpMap_230_ = lean_ctor_get(v___x_222_, 7);
v_anchors_231_ = lean_ctor_get(v___x_222_, 8);
v_instanceMap_232_ = lean_ctor_get(v___x_222_, 9);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_283_ == 0)
{
v___x_234_ = v___x_222_;
v_isShared_235_ = v_isSharedCheck_283_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_instanceMap_232_);
lean_inc(v_anchors_231_);
lean_inc(v_reflCmpMap_230_);
lean_inc(v_lawfulEqCmpMap_229_);
lean_inc(v_ematchDiags_228_);
lean_inc(v_splitDiags_227_);
lean_inc(v_counters_226_);
lean_inc(v_lastTag_225_);
lean_inc(v_simp_224_);
lean_inc(v_congrThms_223_);
lean_dec(v___x_222_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_283_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_236_ = lean_unsigned_to_nat(32u);
v___x_237_ = lean_mk_empty_array_with_capacity(v___x_236_);
lean_dec_ref(v___x_237_);
v___x_238_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_238_);
v___x_240_ = v___x_234_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_congrThms_223_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_lastTag_225_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_counters_226_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_splitDiags_227_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v_ematchDiags_228_);
lean_ctor_set(v_reuseFailAlloc_282_, 6, v_lawfulEqCmpMap_229_);
lean_ctor_set(v_reuseFailAlloc_282_, 7, v_reflCmpMap_230_);
lean_ctor_set(v_reuseFailAlloc_282_, 8, v_anchors_231_);
lean_ctor_set(v_reuseFailAlloc_282_, 9, v_instanceMap_232_);
v___x_240_ = v_reuseFailAlloc_282_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v_simp_242_; lean_object* v_simpMethods_243_; lean_object* v___x_244_; 
v___x_241_ = lean_st_ref_put(v___y_214_, v___x_240_);
v_simp_242_ = lean_ctor_get(v___y_213_, 0);
v_simpMethods_243_ = lean_ctor_get(v___y_213_, 1);
lean_inc_ref(v_simpMethods_243_);
lean_inc_ref(v_simp_242_);
v___x_244_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_211_, v_simp_242_, v_simp_224_, v_simpMethods_243_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_273_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_273_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_273_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_273_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_fst_249_; lean_object* v_snd_250_; lean_object* v___x_251_; lean_object* v_congrThms_252_; lean_object* v_lastTag_253_; lean_object* v_counters_254_; lean_object* v_splitDiags_255_; lean_object* v_ematchDiags_256_; lean_object* v_lawfulEqCmpMap_257_; lean_object* v_reflCmpMap_258_; lean_object* v_anchors_259_; lean_object* v_instanceMap_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_271_; 
v_fst_249_ = lean_ctor_get(v_a_245_, 0);
lean_inc(v_fst_249_);
v_snd_250_ = lean_ctor_get(v_a_245_, 1);
lean_inc(v_snd_250_);
lean_dec(v_a_245_);
v___x_251_ = lean_st_ref_take(v___y_214_);
v_congrThms_252_ = lean_ctor_get(v___x_251_, 0);
v_lastTag_253_ = lean_ctor_get(v___x_251_, 2);
v_counters_254_ = lean_ctor_get(v___x_251_, 3);
v_splitDiags_255_ = lean_ctor_get(v___x_251_, 4);
v_ematchDiags_256_ = lean_ctor_get(v___x_251_, 5);
v_lawfulEqCmpMap_257_ = lean_ctor_get(v___x_251_, 6);
v_reflCmpMap_258_ = lean_ctor_get(v___x_251_, 7);
v_anchors_259_ = lean_ctor_get(v___x_251_, 8);
v_instanceMap_260_ = lean_ctor_get(v___x_251_, 9);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v___x_251_, 1);
lean_dec(v_unused_272_);
v___x_262_ = v___x_251_;
v_isShared_263_ = v_isSharedCheck_271_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_instanceMap_260_);
lean_inc(v_anchors_259_);
lean_inc(v_reflCmpMap_258_);
lean_inc(v_lawfulEqCmpMap_257_);
lean_inc(v_ematchDiags_256_);
lean_inc(v_splitDiags_255_);
lean_inc(v_counters_254_);
lean_inc(v_lastTag_253_);
lean_inc(v_congrThms_252_);
lean_dec(v___x_251_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_271_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_snd_250_);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_congrThms_252_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_snd_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v_lastTag_253_);
lean_ctor_set(v_reuseFailAlloc_270_, 3, v_counters_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 4, v_splitDiags_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 5, v_ematchDiags_256_);
lean_ctor_set(v_reuseFailAlloc_270_, 6, v_lawfulEqCmpMap_257_);
lean_ctor_set(v_reuseFailAlloc_270_, 7, v_reflCmpMap_258_);
lean_ctor_set(v_reuseFailAlloc_270_, 8, v_anchors_259_);
lean_ctor_set(v_reuseFailAlloc_270_, 9, v_instanceMap_260_);
v___x_265_ = v_reuseFailAlloc_270_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_st_ref_put(v___y_214_, v___x_265_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_fst_249_);
v___x_268_ = v___x_247_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_fst_249_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_244_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_244_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* v_e_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Grind_dsimpCore___lam__0(v_e_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_toCold_308_; lean_object* v_options_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_toCold_308_ = lean_ctor_get(v_a_305_, 0);
v_options_309_ = lean_ctor_get(v_toCold_308_, 2);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_310_, 0, v_e_297_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Grind_dsimpCore___closed__0));
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_311_, v_options_309_, v___f_310_, v___x_312_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Meta_Grind_dsimpCore(v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_Expr_hasMVar(v_e_326_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_e_326_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v_mctx_332_; lean_object* v___x_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; lean_object* v_cache_337_; lean_object* v_zetaDeltaFVarIds_338_; lean_object* v_postponed_339_; lean_object* v_diag_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_349_; 
v___x_331_ = lean_st_ref_get(v___y_327_);
v_mctx_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc_ref(v_mctx_332_);
lean_dec(v___x_331_);
v___x_333_ = l_Lean_instantiateMVarsCore(v_mctx_332_, v_e_326_);
v_fst_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_snd_335_);
lean_dec_ref(v___x_333_);
v___x_336_ = lean_st_ref_take(v___y_327_);
v_cache_337_ = lean_ctor_get(v___x_336_, 1);
v_zetaDeltaFVarIds_338_ = lean_ctor_get(v___x_336_, 2);
v_postponed_339_ = lean_ctor_get(v___x_336_, 3);
v_diag_340_ = lean_ctor_get(v___x_336_, 4);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v___x_336_, 0);
lean_dec(v_unused_350_);
v___x_342_ = v___x_336_;
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_diag_340_);
lean_inc(v_postponed_339_);
lean_inc(v_zetaDeltaFVarIds_338_);
lean_inc(v_cache_337_);
lean_dec(v___x_336_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_snd_335_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_snd_335_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_cache_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_zetaDeltaFVarIds_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_postponed_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_diag_340_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_st_ref_put(v___y_327_, v___x_345_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_fst_334_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_351_, v___y_352_);
lean_dec(v___y_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_355_, v___y_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v___x_389_; lean_object* v_toCold_390_; lean_object* v_mctx_391_; lean_object* v_lctx_392_; lean_object* v_options_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_387_ = lean_st_ref_get(v___y_385_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = lean_st_ref_get(v___y_383_);
v_toCold_390_ = lean_ctor_get(v___y_384_, 0);
v_mctx_391_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_mctx_391_);
lean_dec(v___x_389_);
v_lctx_392_ = lean_ctor_get(v___y_382_, 2);
v_options_393_ = lean_ctor_get(v_toCold_390_, 2);
lean_inc_ref(v_options_393_);
lean_inc_ref(v_lctx_392_);
v___x_394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_394_, 0, v_env_388_);
lean_ctor_set(v___x_394_, 1, v_mctx_391_);
lean_ctor_set(v___x_394_, 2, v_lctx_392_);
lean_ctor_set(v___x_394_, 3, v_options_393_);
v___x_395_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_msgData_381_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_404_; double v___x_405_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_float_of_nat(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_ref_416_; lean_object* v___x_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_462_; 
v_ref_416_ = lean_ctor_get(v___y_413_, 2);
v___x_417_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_462_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_462_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_462_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v_traceState_423_; lean_object* v_env_424_; lean_object* v_nextMacroScope_425_; lean_object* v_ngen_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_cache_428_; lean_object* v_messages_429_; lean_object* v_infoState_430_; lean_object* v_snapshotTasks_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_461_; 
v___x_422_ = lean_st_ref_take(v___y_414_);
v_traceState_423_ = lean_ctor_get(v___x_422_, 4);
v_env_424_ = lean_ctor_get(v___x_422_, 0);
v_nextMacroScope_425_ = lean_ctor_get(v___x_422_, 1);
v_ngen_426_ = lean_ctor_get(v___x_422_, 2);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_422_, 3);
v_cache_428_ = lean_ctor_get(v___x_422_, 5);
v_messages_429_ = lean_ctor_get(v___x_422_, 6);
v_infoState_430_ = lean_ctor_get(v___x_422_, 7);
v_snapshotTasks_431_ = lean_ctor_get(v___x_422_, 8);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_461_ == 0)
{
v___x_433_ = v___x_422_;
v_isShared_434_ = v_isSharedCheck_461_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snapshotTasks_431_);
lean_inc(v_infoState_430_);
lean_inc(v_messages_429_);
lean_inc(v_cache_428_);
lean_inc(v_traceState_423_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_ngen_426_);
lean_inc(v_nextMacroScope_425_);
lean_inc(v_env_424_);
lean_dec(v___x_422_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_461_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint64_t v_tid_435_; lean_object* v_traces_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_460_; 
v_tid_435_ = lean_ctor_get_uint64(v_traceState_423_, sizeof(void*)*1);
v_traces_436_ = lean_ctor_get(v_traceState_423_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_traceState_423_);
if (v_isSharedCheck_460_ == 0)
{
v___x_438_ = v_traceState_423_;
v_isShared_439_ = v_isSharedCheck_460_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_traces_436_);
lean_dec(v_traceState_423_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_460_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; double v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_442_ = 0;
v___x_443_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_444_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_444_, 0, v_cls_409_);
lean_ctor_set(v___x_444_, 1, v___x_440_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set_float(v___x_444_, sizeof(void*)*3, v___x_441_);
lean_ctor_set_float(v___x_444_, sizeof(void*)*3 + 8, v___x_441_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*3 + 16, v___x_442_);
v___x_445_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_446_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v_a_418_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
lean_inc(v_ref_416_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_ref_416_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_PersistentArray_push___redArg(v_traces_436_, v___x_447_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_448_);
v___x_450_ = v___x_438_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_448_);
lean_ctor_set_uint64(v_reuseFailAlloc_459_, sizeof(void*)*1, v_tid_435_);
v___x_450_ = v_reuseFailAlloc_459_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v___x_450_);
v___x_452_ = v___x_433_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_env_424_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_ngen_426_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_458_, 5, v_cache_428_);
lean_ctor_set(v_reuseFailAlloc_458_, 6, v_messages_429_);
lean_ctor_set(v_reuseFailAlloc_458_, 7, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_458_, 8, v_snapshotTasks_431_);
v___x_452_ = v_reuseFailAlloc_458_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = lean_st_ref_put(v___y_414_, v___x_452_);
v___x_454_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_454_);
v___x_456_ = v___x_420_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_463_, v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_481_ = l_Lean_Name_append(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v_a_498_; lean_object* v___x_499_; 
v___x_497_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_485_, v_a_493_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc_n(v_a_498_, 2);
lean_dec_ref(v___x_497_);
v___x_499_ = l_Lean_Meta_Grind_simpCore(v_a_498_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v_expr_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v_expr_501_ = lean_ctor_get(v_a_500_, 0);
lean_inc_ref(v_expr_501_);
v___x_502_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_501_, v_a_493_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v___x_504_ = l_Lean_Meta_Sym_unfoldReducible(v_a_503_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_505_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_507_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_509_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_Lean_Meta_Grind_foldProjs(v_a_511_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = l_Lean_Meta_Sym_normalizeLevels(v_a_513_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_515_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc_n(v_a_517_, 2);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_500_, v_a_517_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_expr_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_expr_520_ = lean_ctor_get(v_a_517_, 0);
lean_inc_ref(v_expr_520_);
lean_dec(v_a_517_);
v___x_521_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_520_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_n(v_a_522_, 2);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_519_, v_a_522_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v_expr_525_; lean_object* v___x_526_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v_expr_525_ = lean_ctor_get(v_a_522_, 0);
lean_inc_ref(v_expr_525_);
lean_dec(v_a_522_);
v___x_526_ = l_Lean_Meta_Sym_canon(v_expr_525_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Meta_Sym_shareCommon(v_a_527_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_577_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_577_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_577_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_577_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_toCold_547_; lean_object* v_options_548_; uint8_t v_hasTrace_549_; 
v_toCold_547_ = lean_ctor_get(v_a_494_, 0);
v_options_548_ = lean_ctor_get(v_toCold_547_, 2);
v_hasTrace_549_ = lean_ctor_get_uint8(v_options_548_, sizeof(void*)*1);
if (v_hasTrace_549_ == 0)
{
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
goto v___jp_533_;
}
else
{
lean_object* v_inheritedTraceOptions_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_inheritedTraceOptions_550_ = lean_ctor_get(v_toCold_547_, 11);
v___x_551_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_552_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_553_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_550_, v_options_548_, v___x_552_);
if (v___x_553_ == 0)
{
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
goto v___jp_533_;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_Grind_updateLastTag(v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref_known(v___x_554_, 1);
v___x_555_ = l_Lean_MessageData_ofExpr(v_a_498_);
v___x_556_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_inc(v_a_529_);
v___x_558_ = l_Lean_MessageData_ofExpr(v_a_529_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_551_, v___x_559_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec_ref_known(v___x_560_, 1);
goto v___jp_533_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_531_);
lean_dec(v_a_529_);
lean_dec(v_a_524_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
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
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_del_object(v___x_531_);
lean_dec(v_a_529_);
lean_dec(v_a_524_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
v_a_569_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_554_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_554_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
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
}
v___jp_533_:
{
lean_object* v_proof_x3f_534_; uint8_t v_cache_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_545_; 
v_proof_x3f_534_ = lean_ctor_get(v_a_524_, 1);
v_cache_535_ = lean_ctor_get_uint8(v_a_524_, sizeof(void*)*2);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_524_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_a_524_, 0);
lean_dec(v_unused_546_);
v___x_537_ = v_a_524_;
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_proof_x3f_534_);
lean_dec(v_a_524_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_545_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_a_529_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_529_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_proof_x3f_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_544_, sizeof(void*)*2, v_cache_535_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_540_);
v___x_542_ = v___x_531_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_524_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_578_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_528_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_528_);
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
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_524_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_586_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_526_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_526_);
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
lean_dec(v_a_522_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v___x_523_;
}
}
else
{
lean_dec(v_a_519_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v___x_521_;
}
}
else
{
lean_dec(v_a_517_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v___x_518_;
}
}
else
{
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v___x_516_;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_594_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_514_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_514_);
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
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_602_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_512_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_512_);
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
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_610_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_510_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_510_);
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
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_618_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_508_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_508_);
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
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_626_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_506_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_506_);
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
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
v_a_634_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_504_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_504_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_dec(v_a_498_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec(v_a_486_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = lean_grind_preprocess(v_e_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_655_, v_msg_656_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_669_, lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_669_, v_msg_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
return v_res_682_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_690_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_691_ = l_Lean_Name_append(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_704_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_705_ = l_Lean_mkConst(v___x_704_, v___x_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_706_, lean_object* v_proof_707_, lean_object* v_generation_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
lean_inc(v_a_718_);
lean_inc_ref(v_a_717_);
lean_inc(v_a_716_);
lean_inc_ref(v_a_715_);
lean_inc(v_a_714_);
lean_inc_ref(v_a_713_);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc(v_a_709_);
lean_inc_ref(v_prop_706_);
v___x_720_ = lean_grind_preprocess(v_prop_706_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_790_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_790_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_790_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_790_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_expr_725_; lean_object* v_proof_x3f_726_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_773_; 
v_expr_725_ = lean_ctor_get(v_a_721_, 0);
lean_inc_ref(v_expr_725_);
v_proof_x3f_726_ = lean_ctor_get(v_a_721_, 1);
lean_inc(v_proof_x3f_726_);
lean_dec(v_a_721_);
if (lean_obj_tag(v_proof_x3f_726_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_val_787_ = lean_ctor_get(v_proof_x3f_726_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_proof_x3f_726_, 1);
v___x_788_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_725_);
lean_inc_ref(v_prop_706_);
v___x_789_ = l_Lean_mkApp4(v___x_788_, v_prop_706_, v_expr_725_, v_val_787_, v_proof_707_);
v___y_773_ = v___x_789_;
goto v___jp_772_;
}
else
{
lean_dec(v_proof_x3f_726_);
v___y_773_ = v_proof_707_;
goto v___jp_772_;
}
v___jp_727_:
{
lean_object* v___x_730_; lean_object* v_toGoalState_731_; lean_object* v_mvarId_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_771_; 
v___x_730_ = lean_st_ref_take(v___y_729_);
v_toGoalState_731_ = lean_ctor_get(v___x_730_, 0);
v_mvarId_732_ = lean_ctor_get(v___x_730_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_771_ == 0)
{
v___x_734_ = v___x_730_;
v_isShared_735_ = v_isSharedCheck_771_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_mvarId_732_);
lean_inc(v_toGoalState_731_);
lean_dec(v___x_730_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_771_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_nextDeclIdx_736_; lean_object* v_enodeMap_737_; lean_object* v_exprs_738_; lean_object* v_parents_739_; lean_object* v_congrTable_740_; lean_object* v_appMap_741_; lean_object* v_indicesFound_742_; lean_object* v_newFacts_743_; uint8_t v_inconsistent_744_; lean_object* v_nextIdx_745_; lean_object* v_newRawFacts_746_; lean_object* v_facts_747_; lean_object* v_extThms_748_; lean_object* v_ematch_749_; lean_object* v_inj_750_; lean_object* v_split_751_; lean_object* v_clean_752_; lean_object* v_sstates_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_770_; 
v_nextDeclIdx_736_ = lean_ctor_get(v_toGoalState_731_, 0);
v_enodeMap_737_ = lean_ctor_get(v_toGoalState_731_, 1);
v_exprs_738_ = lean_ctor_get(v_toGoalState_731_, 2);
v_parents_739_ = lean_ctor_get(v_toGoalState_731_, 3);
v_congrTable_740_ = lean_ctor_get(v_toGoalState_731_, 4);
v_appMap_741_ = lean_ctor_get(v_toGoalState_731_, 5);
v_indicesFound_742_ = lean_ctor_get(v_toGoalState_731_, 6);
v_newFacts_743_ = lean_ctor_get(v_toGoalState_731_, 7);
v_inconsistent_744_ = lean_ctor_get_uint8(v_toGoalState_731_, sizeof(void*)*17);
v_nextIdx_745_ = lean_ctor_get(v_toGoalState_731_, 8);
v_newRawFacts_746_ = lean_ctor_get(v_toGoalState_731_, 9);
v_facts_747_ = lean_ctor_get(v_toGoalState_731_, 10);
v_extThms_748_ = lean_ctor_get(v_toGoalState_731_, 11);
v_ematch_749_ = lean_ctor_get(v_toGoalState_731_, 12);
v_inj_750_ = lean_ctor_get(v_toGoalState_731_, 13);
v_split_751_ = lean_ctor_get(v_toGoalState_731_, 14);
v_clean_752_ = lean_ctor_get(v_toGoalState_731_, 15);
v_sstates_753_ = lean_ctor_get(v_toGoalState_731_, 16);
v_isSharedCheck_770_ = !lean_is_exclusive(v_toGoalState_731_);
if (v_isSharedCheck_770_ == 0)
{
v___x_755_ = v_toGoalState_731_;
v_isShared_756_ = v_isSharedCheck_770_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_sstates_753_);
lean_inc(v_clean_752_);
lean_inc(v_split_751_);
lean_inc(v_inj_750_);
lean_inc(v_ematch_749_);
lean_inc(v_extThms_748_);
lean_inc(v_facts_747_);
lean_inc(v_newRawFacts_746_);
lean_inc(v_nextIdx_745_);
lean_inc(v_newFacts_743_);
lean_inc(v_indicesFound_742_);
lean_inc(v_appMap_741_);
lean_inc(v_congrTable_740_);
lean_inc(v_parents_739_);
lean_inc(v_exprs_738_);
lean_inc(v_enodeMap_737_);
lean_inc(v_nextDeclIdx_736_);
lean_dec(v_toGoalState_731_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_770_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_757_, 0, v_expr_725_);
lean_ctor_set(v___x_757_, 1, v___y_728_);
lean_ctor_set(v___x_757_, 2, v_generation_708_);
v___x_758_ = lean_array_push(v_newFacts_743_, v___x_757_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 7, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_nextDeclIdx_736_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_enodeMap_737_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_exprs_738_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_parents_739_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_congrTable_740_);
lean_ctor_set(v_reuseFailAlloc_769_, 5, v_appMap_741_);
lean_ctor_set(v_reuseFailAlloc_769_, 6, v_indicesFound_742_);
lean_ctor_set(v_reuseFailAlloc_769_, 7, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_769_, 8, v_nextIdx_745_);
lean_ctor_set(v_reuseFailAlloc_769_, 9, v_newRawFacts_746_);
lean_ctor_set(v_reuseFailAlloc_769_, 10, v_facts_747_);
lean_ctor_set(v_reuseFailAlloc_769_, 11, v_extThms_748_);
lean_ctor_set(v_reuseFailAlloc_769_, 12, v_ematch_749_);
lean_ctor_set(v_reuseFailAlloc_769_, 13, v_inj_750_);
lean_ctor_set(v_reuseFailAlloc_769_, 14, v_split_751_);
lean_ctor_set(v_reuseFailAlloc_769_, 15, v_clean_752_);
lean_ctor_set(v_reuseFailAlloc_769_, 16, v_sstates_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*17, v_inconsistent_744_);
v___x_760_ = v_reuseFailAlloc_769_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_760_);
v___x_762_ = v___x_734_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_mvarId_732_);
v___x_762_ = v_reuseFailAlloc_768_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_763_ = lean_st_ref_put(v___y_729_, v___x_762_);
v___x_764_ = lean_box(0);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_764_);
v___x_766_ = v___x_723_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
v___jp_772_:
{
lean_object* v_toCold_774_; lean_object* v_options_775_; uint8_t v_hasTrace_776_; 
v_toCold_774_ = lean_ctor_get(v_a_717_, 0);
v_options_775_ = lean_ctor_get(v_toCold_774_, 2);
v_hasTrace_776_ = lean_ctor_get_uint8(v_options_775_, sizeof(void*)*1);
if (v_hasTrace_776_ == 0)
{
lean_dec_ref(v_prop_706_);
v___y_728_ = v___y_773_;
v___y_729_ = v_a_709_;
goto v___jp_727_;
}
else
{
lean_object* v_inheritedTraceOptions_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_inheritedTraceOptions_777_ = lean_ctor_get(v_toCold_774_, 11);
v___x_778_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_779_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_777_, v_options_775_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec_ref(v_prop_706_);
v___y_728_ = v___y_773_;
v___y_729_ = v_a_709_;
goto v___jp_727_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_781_ = l_Lean_MessageData_ofExpr(v_prop_706_);
v___x_782_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_inc_ref(v_expr_725_);
v___x_784_ = l_Lean_MessageData_ofExpr(v_expr_725_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_778_, v___x_785_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v___y_728_ = v___y_773_;
v___y_729_ = v_a_709_;
goto v___jp_727_;
}
else
{
lean_dec_ref(v___y_773_);
lean_dec_ref(v_expr_725_);
lean_del_object(v___x_723_);
lean_dec(v_generation_708_);
return v___x_786_;
}
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_generation_708_);
lean_dec_ref(v_proof_707_);
lean_dec_ref(v_prop_706_);
v_a_791_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_720_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_720_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_799_, lean_object* v_proof_800_, lean_object* v_generation_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_799_, v_proof_800_, v_generation_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec(v_a_802_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_814_, lean_object* v_generation_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
lean_inc(v_a_825_);
lean_inc_ref(v_a_824_);
lean_inc(v_a_823_);
lean_inc_ref(v_a_822_);
lean_inc_ref(v_proof_814_);
v___x_827_ = lean_infer_type(v_proof_814_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_toCold_828_; lean_object* v_options_829_; uint8_t v_hasTrace_830_; 
v_toCold_828_ = lean_ctor_get(v_a_824_, 0);
v_options_829_ = lean_ctor_get(v_toCold_828_, 2);
v_hasTrace_830_ = lean_ctor_get_uint8(v_options_829_, sizeof(void*)*1);
if (v_hasTrace_830_ == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_827_, 1);
v___x_832_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_831_, v_proof_814_, v_generation_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_832_;
}
else
{
lean_object* v_a_833_; lean_object* v_inheritedTraceOptions_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_a_833_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_827_, 1);
v_inheritedTraceOptions_834_ = lean_ctor_get(v_toCold_828_, 11);
v___x_835_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_836_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_837_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_834_, v_options_829_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_833_, v_proof_814_, v_generation_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_inc(v_a_833_);
v___x_839_ = l_Lean_MessageData_ofExpr(v_a_833_);
v___x_840_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_835_, v___x_839_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
lean_dec_ref_known(v___x_840_, 1);
v___x_841_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_833_, v_proof_814_, v_generation_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_841_;
}
else
{
lean_dec(v_a_833_);
lean_dec(v_generation_815_);
lean_dec_ref(v_proof_814_);
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_generation_815_);
lean_dec_ref(v_proof_814_);
v_a_842_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_827_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_827_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_850_, lean_object* v_generation_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_Grind_pushNewFact(v_proof_850_, v_generation_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec(v_a_852_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; lean_object* v_a_876_; lean_object* v___x_877_; 
v___x_875_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_864_, v_a_871_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = l_Lean_Meta_Sym_unfoldReducible(v_a_876_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_878_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_880_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Meta_Grind_foldProjs(v_a_882_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Meta_Sym_normalizeLevels(v_a_884_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Meta_Sym_canon(v_a_886_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = l_Lean_Meta_Sym_shareCommon(v_a_888_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_889_;
}
else
{
return v___x_887_;
}
}
else
{
return v___x_885_;
}
}
else
{
return v___x_883_;
}
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_902_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_Grind_preprocessLight(v_e_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec(v_a_916_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

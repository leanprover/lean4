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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_simpCore___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__10;
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
lean_object* v_cellCount_64_; lean_object* v___x_65_; 
v_cellCount_64_ = lean_unsigned_to_nat(16u);
v___x_65_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_66_; lean_object* v___x_67_; 
v_cellCount_66_ = lean_unsigned_to_nat(16u);
v___x_67_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__1, &l_Lean_Meta_Grind_simpCore___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1);
v___x_69_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__0, &l_Lean_Meta_Grind_simpCore___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__3, &l_Lean_Meta_Grind_simpCore___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__4, &l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4);
v___x_76_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__2, &l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2);
v___x_77_ = 1;
v___x_78_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_75_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*2, v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__4, &l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(32u);
v___x_83_ = lean_mk_empty_array_with_capacity(v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8(void){
_start:
{
size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__7, &l_Lean_Meta_Grind_simpCore___lam__0___closed__7_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7);
v___x_90_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_86_);
lean_ctor_set(v___x_90_, 3, v___x_86_);
lean_ctor_set_usize(v___x_90_, 4, v___x_85_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__8, &l_Lean_Meta_Grind_simpCore___lam__0___closed__8_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__4, &l_Lean_Meta_Grind_simpCore___lam__0___closed__4_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
lean_ctor_set(v___x_93_, 3, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__10(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__9, &l_Lean_Meta_Grind_simpCore___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__6, &l_Lean_Meta_Grind_simpCore___lam__0___closed__6_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6);
v___x_97_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__2, &l_Lean_Meta_Grind_simpCore___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2);
v___x_98_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__5, &l_Lean_Meta_Grind_simpCore___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5);
v___x_99_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_97_);
lean_ctor_set(v___x_99_, 3, v___x_96_);
lean_ctor_set(v___x_99_, 4, v___x_95_);
lean_ctor_set(v___x_99_, 5, v___x_94_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object* v_e_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_congrThms_112_; lean_object* v_simp_113_; lean_object* v_lastTag_114_; lean_object* v_counters_115_; lean_object* v_splitDiags_116_; lean_object* v_ematchDiags_117_; lean_object* v_lawfulEqCmpMap_118_; lean_object* v_reflCmpMap_119_; lean_object* v_anchors_120_; lean_object* v_instanceMap_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_170_; 
v___x_111_ = lean_st_ref_take(v___y_103_);
v_congrThms_112_ = lean_ctor_get(v___x_111_, 0);
v_simp_113_ = lean_ctor_get(v___x_111_, 1);
v_lastTag_114_ = lean_ctor_get(v___x_111_, 2);
v_counters_115_ = lean_ctor_get(v___x_111_, 3);
v_splitDiags_116_ = lean_ctor_get(v___x_111_, 4);
v_ematchDiags_117_ = lean_ctor_get(v___x_111_, 5);
v_lawfulEqCmpMap_118_ = lean_ctor_get(v___x_111_, 6);
v_reflCmpMap_119_ = lean_ctor_get(v___x_111_, 7);
v_anchors_120_ = lean_ctor_get(v___x_111_, 8);
v_instanceMap_121_ = lean_ctor_get(v___x_111_, 9);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_170_ == 0)
{
v___x_123_ = v___x_111_;
v_isShared_124_ = v_isSharedCheck_170_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_instanceMap_121_);
lean_inc(v_anchors_120_);
lean_inc(v_reflCmpMap_119_);
lean_inc(v_lawfulEqCmpMap_118_);
lean_inc(v_ematchDiags_117_);
lean_inc(v_splitDiags_116_);
lean_inc(v_counters_115_);
lean_inc(v_lastTag_114_);
lean_inc(v_simp_113_);
lean_inc(v_congrThms_112_);
lean_dec(v___x_111_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_170_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__10, &l_Lean_Meta_Grind_simpCore___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__10);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_congrThms_112_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_lastTag_114_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_counters_115_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_splitDiags_116_);
lean_ctor_set(v_reuseFailAlloc_169_, 5, v_ematchDiags_117_);
lean_ctor_set(v_reuseFailAlloc_169_, 6, v_lawfulEqCmpMap_118_);
lean_ctor_set(v_reuseFailAlloc_169_, 7, v_reflCmpMap_119_);
lean_ctor_set(v_reuseFailAlloc_169_, 8, v_anchors_120_);
lean_ctor_set(v_reuseFailAlloc_169_, 9, v_instanceMap_121_);
v___x_127_ = v_reuseFailAlloc_169_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v_simp_129_; lean_object* v_simpMethods_130_; lean_object* v___x_131_; 
v___x_128_ = lean_st_ref_put(v___y_103_, v___x_127_);
v_simp_129_ = lean_ctor_get(v___y_102_, 0);
v_simpMethods_130_ = lean_ctor_get(v___y_102_, 1);
lean_inc_ref(v_simpMethods_130_);
lean_inc_ref(v_simp_129_);
v___x_131_ = l_Lean_Meta_Simp_mainCore(v_e_100_, v_simp_129_, v_simp_113_, v_simpMethods_130_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_160_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_160_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_160_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_160_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_138_; lean_object* v_congrThms_139_; lean_object* v_lastTag_140_; lean_object* v_counters_141_; lean_object* v_splitDiags_142_; lean_object* v_ematchDiags_143_; lean_object* v_lawfulEqCmpMap_144_; lean_object* v_reflCmpMap_145_; lean_object* v_anchors_146_; lean_object* v_instanceMap_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_158_; 
v_fst_136_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_fst_136_);
v_snd_137_ = lean_ctor_get(v_a_132_, 1);
lean_inc(v_snd_137_);
lean_dec(v_a_132_);
v___x_138_ = lean_st_ref_take(v___y_103_);
v_congrThms_139_ = lean_ctor_get(v___x_138_, 0);
v_lastTag_140_ = lean_ctor_get(v___x_138_, 2);
v_counters_141_ = lean_ctor_get(v___x_138_, 3);
v_splitDiags_142_ = lean_ctor_get(v___x_138_, 4);
v_ematchDiags_143_ = lean_ctor_get(v___x_138_, 5);
v_lawfulEqCmpMap_144_ = lean_ctor_get(v___x_138_, 6);
v_reflCmpMap_145_ = lean_ctor_get(v___x_138_, 7);
v_anchors_146_ = lean_ctor_get(v___x_138_, 8);
v_instanceMap_147_ = lean_ctor_get(v___x_138_, 9);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_138_, 1);
lean_dec(v_unused_159_);
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_instanceMap_147_);
lean_inc(v_anchors_146_);
lean_inc(v_reflCmpMap_145_);
lean_inc(v_lawfulEqCmpMap_144_);
lean_inc(v_ematchDiags_143_);
lean_inc(v_splitDiags_142_);
lean_inc(v_counters_141_);
lean_inc(v_lastTag_140_);
lean_inc(v_congrThms_139_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_snd_137_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_congrThms_139_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_snd_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_lastTag_140_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_counters_141_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_splitDiags_142_);
lean_ctor_set(v_reuseFailAlloc_157_, 5, v_ematchDiags_143_);
lean_ctor_set(v_reuseFailAlloc_157_, 6, v_lawfulEqCmpMap_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 7, v_reflCmpMap_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 8, v_anchors_146_);
lean_ctor_set(v_reuseFailAlloc_157_, 9, v_instanceMap_147_);
v___x_152_ = v_reuseFailAlloc_157_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_st_ref_put(v___y_103_, v___x_152_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v_fst_136_);
v___x_155_ = v___x_134_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_fst_136_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_131_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_131_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object* v_e_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Grind_simpCore___lam__0(v_e_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_options_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_options_195_ = lean_ctor_get(v_a_192_, 2);
v___f_196_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_196_, 0, v_e_184_);
v___x_197_ = ((lean_object*)(l_Lean_Meta_Grind_simpCore___closed__0));
v___x_198_ = lean_box(0);
v___x_199_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_197_, v_options_195_, v___f_196_, v___x_198_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Grind_simpCore(v_e_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* v_e_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_congrThms_224_; lean_object* v_simp_225_; lean_object* v_lastTag_226_; lean_object* v_counters_227_; lean_object* v_splitDiags_228_; lean_object* v_ematchDiags_229_; lean_object* v_lawfulEqCmpMap_230_; lean_object* v_reflCmpMap_231_; lean_object* v_anchors_232_; lean_object* v_instanceMap_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_284_; 
v___x_223_ = lean_st_ref_take(v___y_215_);
v_congrThms_224_ = lean_ctor_get(v___x_223_, 0);
v_simp_225_ = lean_ctor_get(v___x_223_, 1);
v_lastTag_226_ = lean_ctor_get(v___x_223_, 2);
v_counters_227_ = lean_ctor_get(v___x_223_, 3);
v_splitDiags_228_ = lean_ctor_get(v___x_223_, 4);
v_ematchDiags_229_ = lean_ctor_get(v___x_223_, 5);
v_lawfulEqCmpMap_230_ = lean_ctor_get(v___x_223_, 6);
v_reflCmpMap_231_ = lean_ctor_get(v___x_223_, 7);
v_anchors_232_ = lean_ctor_get(v___x_223_, 8);
v_instanceMap_233_ = lean_ctor_get(v___x_223_, 9);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_284_ == 0)
{
v___x_235_ = v___x_223_;
v_isShared_236_ = v_isSharedCheck_284_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_instanceMap_233_);
lean_inc(v_anchors_232_);
lean_inc(v_reflCmpMap_231_);
lean_inc(v_lawfulEqCmpMap_230_);
lean_inc(v_ematchDiags_229_);
lean_inc(v_splitDiags_228_);
lean_inc(v_counters_227_);
lean_inc(v_lastTag_226_);
lean_inc(v_simp_225_);
lean_inc(v_congrThms_224_);
lean_dec(v___x_223_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_284_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(32u);
v___x_238_ = lean_mk_empty_array_with_capacity(v___x_237_);
lean_dec_ref(v___x_238_);
v___x_239_ = lean_obj_once(&l_Lean_Meta_Grind_simpCore___lam__0___closed__10, &l_Lean_Meta_Grind_simpCore___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__10);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_239_);
v___x_241_ = v___x_235_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_congrThms_224_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_lastTag_226_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_counters_227_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_splitDiags_228_);
lean_ctor_set(v_reuseFailAlloc_283_, 5, v_ematchDiags_229_);
lean_ctor_set(v_reuseFailAlloc_283_, 6, v_lawfulEqCmpMap_230_);
lean_ctor_set(v_reuseFailAlloc_283_, 7, v_reflCmpMap_231_);
lean_ctor_set(v_reuseFailAlloc_283_, 8, v_anchors_232_);
lean_ctor_set(v_reuseFailAlloc_283_, 9, v_instanceMap_233_);
v___x_241_ = v_reuseFailAlloc_283_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v_simp_243_; lean_object* v_simpMethods_244_; lean_object* v___x_245_; 
v___x_242_ = lean_st_ref_put(v___y_215_, v___x_241_);
v_simp_243_ = lean_ctor_get(v___y_214_, 0);
v_simpMethods_244_ = lean_ctor_get(v___y_214_, 1);
lean_inc_ref(v_simpMethods_244_);
lean_inc_ref(v_simp_243_);
v___x_245_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_212_, v_simp_243_, v_simp_225_, v_simpMethods_244_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_274_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_274_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; lean_object* v_congrThms_253_; lean_object* v_lastTag_254_; lean_object* v_counters_255_; lean_object* v_splitDiags_256_; lean_object* v_ematchDiags_257_; lean_object* v_lawfulEqCmpMap_258_; lean_object* v_reflCmpMap_259_; lean_object* v_anchors_260_; lean_object* v_instanceMap_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_272_; 
v_fst_250_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_a_246_, 1);
lean_inc(v_snd_251_);
lean_dec(v_a_246_);
v___x_252_ = lean_st_ref_take(v___y_215_);
v_congrThms_253_ = lean_ctor_get(v___x_252_, 0);
v_lastTag_254_ = lean_ctor_get(v___x_252_, 2);
v_counters_255_ = lean_ctor_get(v___x_252_, 3);
v_splitDiags_256_ = lean_ctor_get(v___x_252_, 4);
v_ematchDiags_257_ = lean_ctor_get(v___x_252_, 5);
v_lawfulEqCmpMap_258_ = lean_ctor_get(v___x_252_, 6);
v_reflCmpMap_259_ = lean_ctor_get(v___x_252_, 7);
v_anchors_260_ = lean_ctor_get(v___x_252_, 8);
v_instanceMap_261_ = lean_ctor_get(v___x_252_, 9);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_252_, 1);
lean_dec(v_unused_273_);
v___x_263_ = v___x_252_;
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_instanceMap_261_);
lean_inc(v_anchors_260_);
lean_inc(v_reflCmpMap_259_);
lean_inc(v_lawfulEqCmpMap_258_);
lean_inc(v_ematchDiags_257_);
lean_inc(v_splitDiags_256_);
lean_inc(v_counters_255_);
lean_inc(v_lastTag_254_);
lean_inc(v_congrThms_253_);
lean_dec(v___x_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_snd_251_);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_congrThms_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_snd_251_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_lastTag_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_counters_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_splitDiags_256_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v_ematchDiags_257_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_lawfulEqCmpMap_258_);
lean_ctor_set(v_reuseFailAlloc_271_, 7, v_reflCmpMap_259_);
lean_ctor_set(v_reuseFailAlloc_271_, 8, v_anchors_260_);
lean_ctor_set(v_reuseFailAlloc_271_, 9, v_instanceMap_261_);
v___x_266_ = v_reuseFailAlloc_271_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_st_ref_put(v___y_215_, v___x_266_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v_fst_250_);
v___x_269_ = v___x_248_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_fst_250_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_245_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_245_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* v_e_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Grind_dsimpCore___lam__0(v_e_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_options_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_options_309_ = lean_ctor_get(v_a_306_, 2);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_310_, 0, v_e_298_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Grind_dsimpCore___closed__0));
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_profileitM___at___00Lean_Meta_Grind_simpCore_spec__0___redArg(v___x_311_, v_options_309_, v___f_310_, v___x_312_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
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
lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v___x_389_; lean_object* v_mctx_390_; lean_object* v_lctx_391_; lean_object* v_options_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_387_ = lean_st_ref_get(v___y_385_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = lean_st_ref_get(v___y_383_);
v_mctx_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_mctx_390_);
lean_dec(v___x_389_);
v_lctx_391_ = lean_ctor_get(v___y_382_, 2);
v_options_392_ = lean_ctor_get(v___y_384_, 2);
lean_inc_ref(v_options_392_);
lean_inc_ref(v_lctx_391_);
v___x_393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_393_, 0, v_env_388_);
lean_ctor_set(v___x_393_, 1, v_mctx_390_);
lean_ctor_set(v___x_393_, 2, v_lctx_391_);
lean_ctor_set(v___x_393_, 3, v_options_392_);
v___x_394_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_msgData_381_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_402_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_403_; double v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_float_of_nat(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_ref_415_; lean_object* v___x_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_461_; 
v_ref_415_ = lean_ctor_get(v___y_412_, 5);
v___x_416_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_461_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_461_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_461_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v_traceState_422_; lean_object* v_env_423_; lean_object* v_nextMacroScope_424_; lean_object* v_ngen_425_; lean_object* v_auxDeclNGen_426_; lean_object* v_cache_427_; lean_object* v_messages_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_460_; 
v___x_421_ = lean_st_ref_take(v___y_413_);
v_traceState_422_ = lean_ctor_get(v___x_421_, 4);
v_env_423_ = lean_ctor_get(v___x_421_, 0);
v_nextMacroScope_424_ = lean_ctor_get(v___x_421_, 1);
v_ngen_425_ = lean_ctor_get(v___x_421_, 2);
v_auxDeclNGen_426_ = lean_ctor_get(v___x_421_, 3);
v_cache_427_ = lean_ctor_get(v___x_421_, 5);
v_messages_428_ = lean_ctor_get(v___x_421_, 6);
v_infoState_429_ = lean_ctor_get(v___x_421_, 7);
v_snapshotTasks_430_ = lean_ctor_get(v___x_421_, 8);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_460_ == 0)
{
v___x_432_ = v___x_421_;
v_isShared_433_ = v_isSharedCheck_460_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snapshotTasks_430_);
lean_inc(v_infoState_429_);
lean_inc(v_messages_428_);
lean_inc(v_cache_427_);
lean_inc(v_traceState_422_);
lean_inc(v_auxDeclNGen_426_);
lean_inc(v_ngen_425_);
lean_inc(v_nextMacroScope_424_);
lean_inc(v_env_423_);
lean_dec(v___x_421_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_460_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint64_t v_tid_434_; lean_object* v_traces_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_459_; 
v_tid_434_ = lean_ctor_get_uint64(v_traceState_422_, sizeof(void*)*1);
v_traces_435_ = lean_ctor_get(v_traceState_422_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_traceState_422_);
if (v_isSharedCheck_459_ == 0)
{
v___x_437_ = v_traceState_422_;
v_isShared_438_ = v_isSharedCheck_459_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_traces_435_);
lean_dec(v_traceState_422_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_459_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; double v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_441_ = 0;
v___x_442_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_443_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_443_, 0, v_cls_408_);
lean_ctor_set(v___x_443_, 1, v___x_439_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set_float(v___x_443_, sizeof(void*)*3, v___x_440_);
lean_ctor_set_float(v___x_443_, sizeof(void*)*3 + 8, v___x_440_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3 + 16, v___x_441_);
v___x_444_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_445_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v_a_417_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
lean_inc(v_ref_415_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_ref_415_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_PersistentArray_push___redArg(v_traces_435_, v___x_446_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_447_);
v___x_449_ = v___x_437_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_447_);
lean_ctor_set_uint64(v_reuseFailAlloc_458_, sizeof(void*)*1, v_tid_434_);
v___x_449_ = v_reuseFailAlloc_458_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 4, v___x_449_);
v___x_451_ = v___x_432_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_env_423_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_nextMacroScope_424_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_ngen_425_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_auxDeclNGen_426_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_cache_427_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_messages_428_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_snapshotTasks_430_);
v___x_451_ = v_reuseFailAlloc_457_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_st_ref_put(v___y_413_, v___x_451_);
v___x_453_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_453_);
v___x_455_ = v___x_419_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_462_, v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_480_ = l_Lean_Name_append(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_484_, v_a_492_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_n(v_a_497_, 2);
lean_dec_ref(v___x_496_);
v___x_498_ = l_Lean_Meta_Grind_simpCore(v_a_497_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_expr_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v_expr_500_ = lean_ctor_get(v_a_499_, 0);
lean_inc_ref(v_expr_500_);
v___x_501_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_500_, v_a_492_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l_Lean_Meta_Sym_unfoldReducible(v_a_502_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_504_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_506_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_508_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_Grind_foldProjs(v_a_510_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = l_Lean_Meta_Sym_normalizeLevels(v_a_512_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_514_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_n(v_a_516_, 2);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_499_, v_a_516_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v_expr_519_; lean_object* v___x_520_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v_expr_519_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_expr_519_);
lean_dec(v_a_516_);
v___x_520_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_519_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_n(v_a_521_, 2);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_518_, v_a_521_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v_expr_524_; lean_object* v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v_expr_524_ = lean_ctor_get(v_a_521_, 0);
lean_inc_ref(v_expr_524_);
lean_dec(v_a_521_);
v___x_525_ = l_Lean_Meta_Sym_canon(v_expr_524_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Meta_Sym_shareCommon(v_a_526_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_575_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_575_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_575_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_575_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_options_546_; uint8_t v_hasTrace_547_; 
v_options_546_ = lean_ctor_get(v_a_493_, 2);
v_hasTrace_547_ = lean_ctor_get_uint8(v_options_546_, sizeof(void*)*1);
if (v_hasTrace_547_ == 0)
{
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
goto v___jp_532_;
}
else
{
lean_object* v_inheritedTraceOptions_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_inheritedTraceOptions_548_ = lean_ctor_get(v_a_493_, 13);
v___x_549_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_550_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_548_, v_options_546_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
goto v___jp_532_;
}
else
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_Grind_updateLastTag(v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref_known(v___x_552_, 1);
v___x_553_ = l_Lean_MessageData_ofExpr(v_a_497_);
v___x_554_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_inc(v_a_528_);
v___x_556_ = l_Lean_MessageData_ofExpr(v_a_528_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_549_, v___x_557_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_dec_ref_known(v___x_558_, 1);
goto v___jp_532_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_530_);
lean_dec(v_a_528_);
lean_dec(v_a_523_);
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_530_);
lean_dec(v_a_528_);
lean_dec(v_a_523_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
v_a_567_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_552_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_552_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
v___jp_532_:
{
lean_object* v_proof_x3f_533_; uint8_t v_cache_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_544_; 
v_proof_x3f_533_ = lean_ctor_get(v_a_523_, 1);
v_cache_534_ = lean_ctor_get_uint8(v_a_523_, sizeof(void*)*2);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_a_523_, 0);
lean_dec(v_unused_545_);
v___x_536_ = v_a_523_;
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_proof_x3f_533_);
lean_dec(v_a_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_544_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_a_528_);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_528_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_proof_x3f_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_543_, sizeof(void*)*2, v_cache_534_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_539_);
v___x_541_ = v___x_530_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_a_523_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_576_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_527_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_527_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
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
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_523_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_584_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_525_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_525_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_dec(v_a_521_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v___x_522_;
}
}
else
{
lean_dec(v_a_518_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v___x_520_;
}
}
else
{
lean_dec(v_a_516_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v___x_517_;
}
}
else
{
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v___x_515_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_592_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_513_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_513_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_600_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_511_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_511_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_608_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_509_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_509_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_616_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_507_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_507_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_624_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_505_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_505_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
v_a_632_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_503_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_503_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_dec(v_a_497_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = lean_grind_preprocess(v_e_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_653_, v_msg_654_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_667_, lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_667_, v_msg_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec(v___y_669_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_689_ = l_Lean_Name_append(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_702_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_704_, lean_object* v_proof_705_, lean_object* v_generation_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_718_; 
lean_inc(v_a_716_);
lean_inc_ref(v_a_715_);
lean_inc(v_a_714_);
lean_inc_ref(v_a_713_);
lean_inc(v_a_712_);
lean_inc_ref(v_a_711_);
lean_inc(v_a_710_);
lean_inc_ref(v_a_709_);
lean_inc(v_a_708_);
lean_inc(v_a_707_);
lean_inc_ref(v_prop_704_);
v___x_718_ = lean_grind_preprocess(v_prop_704_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_787_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_787_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_787_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_787_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_expr_723_; lean_object* v_proof_x3f_724_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_771_; 
v_expr_723_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_expr_723_);
v_proof_x3f_724_ = lean_ctor_get(v_a_719_, 1);
lean_inc(v_proof_x3f_724_);
lean_dec(v_a_719_);
if (lean_obj_tag(v_proof_x3f_724_) == 1)
{
lean_object* v_val_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_val_784_ = lean_ctor_get(v_proof_x3f_724_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_proof_x3f_724_, 1);
v___x_785_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_723_);
lean_inc_ref(v_prop_704_);
v___x_786_ = l_Lean_mkApp4(v___x_785_, v_prop_704_, v_expr_723_, v_val_784_, v_proof_705_);
v___y_771_ = v___x_786_;
goto v___jp_770_;
}
else
{
lean_dec(v_proof_x3f_724_);
v___y_771_ = v_proof_705_;
goto v___jp_770_;
}
v___jp_725_:
{
lean_object* v___x_728_; lean_object* v_toGoalState_729_; lean_object* v_mvarId_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_769_; 
v___x_728_ = lean_st_ref_take(v___y_727_);
v_toGoalState_729_ = lean_ctor_get(v___x_728_, 0);
v_mvarId_730_ = lean_ctor_get(v___x_728_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_769_ == 0)
{
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_769_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_mvarId_730_);
lean_inc(v_toGoalState_729_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_769_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_nextDeclIdx_734_; lean_object* v_enodeMap_735_; lean_object* v_exprs_736_; lean_object* v_parents_737_; lean_object* v_congrTable_738_; lean_object* v_appMap_739_; lean_object* v_indicesFound_740_; lean_object* v_newFacts_741_; uint8_t v_inconsistent_742_; lean_object* v_nextIdx_743_; lean_object* v_newRawFacts_744_; lean_object* v_facts_745_; lean_object* v_extThms_746_; lean_object* v_ematch_747_; lean_object* v_inj_748_; lean_object* v_split_749_; lean_object* v_clean_750_; lean_object* v_sstates_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_768_; 
v_nextDeclIdx_734_ = lean_ctor_get(v_toGoalState_729_, 0);
v_enodeMap_735_ = lean_ctor_get(v_toGoalState_729_, 1);
v_exprs_736_ = lean_ctor_get(v_toGoalState_729_, 2);
v_parents_737_ = lean_ctor_get(v_toGoalState_729_, 3);
v_congrTable_738_ = lean_ctor_get(v_toGoalState_729_, 4);
v_appMap_739_ = lean_ctor_get(v_toGoalState_729_, 5);
v_indicesFound_740_ = lean_ctor_get(v_toGoalState_729_, 6);
v_newFacts_741_ = lean_ctor_get(v_toGoalState_729_, 7);
v_inconsistent_742_ = lean_ctor_get_uint8(v_toGoalState_729_, sizeof(void*)*17);
v_nextIdx_743_ = lean_ctor_get(v_toGoalState_729_, 8);
v_newRawFacts_744_ = lean_ctor_get(v_toGoalState_729_, 9);
v_facts_745_ = lean_ctor_get(v_toGoalState_729_, 10);
v_extThms_746_ = lean_ctor_get(v_toGoalState_729_, 11);
v_ematch_747_ = lean_ctor_get(v_toGoalState_729_, 12);
v_inj_748_ = lean_ctor_get(v_toGoalState_729_, 13);
v_split_749_ = lean_ctor_get(v_toGoalState_729_, 14);
v_clean_750_ = lean_ctor_get(v_toGoalState_729_, 15);
v_sstates_751_ = lean_ctor_get(v_toGoalState_729_, 16);
v_isSharedCheck_768_ = !lean_is_exclusive(v_toGoalState_729_);
if (v_isSharedCheck_768_ == 0)
{
v___x_753_ = v_toGoalState_729_;
v_isShared_754_ = v_isSharedCheck_768_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_sstates_751_);
lean_inc(v_clean_750_);
lean_inc(v_split_749_);
lean_inc(v_inj_748_);
lean_inc(v_ematch_747_);
lean_inc(v_extThms_746_);
lean_inc(v_facts_745_);
lean_inc(v_newRawFacts_744_);
lean_inc(v_nextIdx_743_);
lean_inc(v_newFacts_741_);
lean_inc(v_indicesFound_740_);
lean_inc(v_appMap_739_);
lean_inc(v_congrTable_738_);
lean_inc(v_parents_737_);
lean_inc(v_exprs_736_);
lean_inc(v_enodeMap_735_);
lean_inc(v_nextDeclIdx_734_);
lean_dec(v_toGoalState_729_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_768_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_755_, 0, v_expr_723_);
lean_ctor_set(v___x_755_, 1, v___y_726_);
lean_ctor_set(v___x_755_, 2, v_generation_706_);
v___x_756_ = lean_array_push(v_newFacts_741_, v___x_755_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 7, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_nextDeclIdx_734_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_enodeMap_735_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_exprs_736_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_parents_737_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_congrTable_738_);
lean_ctor_set(v_reuseFailAlloc_767_, 5, v_appMap_739_);
lean_ctor_set(v_reuseFailAlloc_767_, 6, v_indicesFound_740_);
lean_ctor_set(v_reuseFailAlloc_767_, 7, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_767_, 8, v_nextIdx_743_);
lean_ctor_set(v_reuseFailAlloc_767_, 9, v_newRawFacts_744_);
lean_ctor_set(v_reuseFailAlloc_767_, 10, v_facts_745_);
lean_ctor_set(v_reuseFailAlloc_767_, 11, v_extThms_746_);
lean_ctor_set(v_reuseFailAlloc_767_, 12, v_ematch_747_);
lean_ctor_set(v_reuseFailAlloc_767_, 13, v_inj_748_);
lean_ctor_set(v_reuseFailAlloc_767_, 14, v_split_749_);
lean_ctor_set(v_reuseFailAlloc_767_, 15, v_clean_750_);
lean_ctor_set(v_reuseFailAlloc_767_, 16, v_sstates_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*17, v_inconsistent_742_);
v___x_758_ = v_reuseFailAlloc_767_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_758_);
v___x_760_ = v___x_732_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_mvarId_730_);
v___x_760_ = v_reuseFailAlloc_766_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = lean_st_ref_put(v___y_727_, v___x_760_);
v___x_762_ = lean_box(0);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_762_);
v___x_764_ = v___x_721_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
v___jp_770_:
{
lean_object* v_options_772_; uint8_t v_hasTrace_773_; 
v_options_772_ = lean_ctor_get(v_a_715_, 2);
v_hasTrace_773_ = lean_ctor_get_uint8(v_options_772_, sizeof(void*)*1);
if (v_hasTrace_773_ == 0)
{
lean_dec_ref(v_prop_704_);
v___y_726_ = v___y_771_;
v___y_727_ = v_a_707_;
goto v___jp_725_;
}
else
{
lean_object* v_inheritedTraceOptions_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_inheritedTraceOptions_774_ = lean_ctor_get(v_a_715_, 13);
v___x_775_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_776_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_774_, v_options_772_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec_ref(v_prop_704_);
v___y_726_ = v___y_771_;
v___y_727_ = v_a_707_;
goto v___jp_725_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_778_ = l_Lean_MessageData_ofExpr(v_prop_704_);
v___x_779_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
lean_inc_ref(v_expr_723_);
v___x_781_ = l_Lean_MessageData_ofExpr(v_expr_723_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_775_, v___x_782_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_dec_ref_known(v___x_783_, 1);
v___y_726_ = v___y_771_;
v___y_727_ = v_a_707_;
goto v___jp_725_;
}
else
{
lean_dec_ref(v___y_771_);
lean_dec_ref(v_expr_723_);
lean_del_object(v___x_721_);
lean_dec(v_generation_706_);
return v___x_783_;
}
}
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_generation_706_);
lean_dec_ref(v_proof_705_);
lean_dec_ref(v_prop_704_);
v_a_788_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_718_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_718_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_796_, lean_object* v_proof_797_, lean_object* v_generation_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_796_, v_proof_797_, v_generation_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_811_, lean_object* v_generation_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; 
lean_inc(v_a_822_);
lean_inc_ref(v_a_821_);
lean_inc(v_a_820_);
lean_inc_ref(v_a_819_);
lean_inc_ref(v_proof_811_);
v___x_824_ = lean_infer_type(v_proof_811_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_options_825_; uint8_t v_hasTrace_826_; 
v_options_825_ = lean_ctor_get(v_a_821_, 2);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
if (v_hasTrace_826_ == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_824_, 1);
v___x_828_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_827_, v_proof_811_, v_generation_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_828_;
}
else
{
lean_object* v_a_829_; lean_object* v_inheritedTraceOptions_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_a_829_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_824_, 1);
v_inheritedTraceOptions_830_ = lean_ctor_get(v_a_821_, 13);
v___x_831_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_832_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_830_, v_options_825_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_829_, v_proof_811_, v_generation_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc(v_a_829_);
v___x_835_ = l_Lean_MessageData_ofExpr(v_a_829_);
v___x_836_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_831_, v___x_835_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_837_; 
lean_dec_ref_known(v___x_836_, 1);
v___x_837_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_829_, v_proof_811_, v_generation_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_837_;
}
else
{
lean_dec(v_a_829_);
lean_dec(v_generation_812_);
lean_dec_ref(v_proof_811_);
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_generation_812_);
lean_dec_ref(v_proof_811_);
v_a_838_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_824_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_824_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_846_, lean_object* v_generation_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Grind_pushNewFact(v_proof_846_, v_generation_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec(v_a_848_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; lean_object* v_a_872_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_860_, v_a_867_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = l_Lean_Meta_Sym_unfoldReducible(v_a_872_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_874_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_876_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = l_Lean_Meta_Grind_foldProjs(v_a_878_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = l_Lean_Meta_Sym_normalizeLevels(v_a_880_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Meta_Sym_canon(v_a_882_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Meta_Sym_shareCommon(v_a_884_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
return v___x_885_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_898_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Grind_preprocessLight(v_e_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec(v_a_912_);
return v_res_923_;
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

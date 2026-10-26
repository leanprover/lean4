// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Simp.Main public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.MatchDiscrOnly import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons import Lean.Meta.Sym.Util import Lean.Meta.Sym.Simp.Main import Lean.Meta.Sym.DSimp.Main
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFactCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Meta_Grind_backward_grind_normalizer;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_dsimpMainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_abstractNestedProofs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_symNorm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_symNorm___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_symNorm___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_symNorm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_symNorm___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_symNorm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_symNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_symNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind dsimp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg(lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_17_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_15_);
v___x_18_ = l_Lean_Meta_Grind_backward_grind_normalizer;
v___x_19_ = l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(v___x_17_, v___x_18_);
lean_dec_ref(v___x_17_);
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg___boxed(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_22_);
lean_dec_ref(v_a_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer(lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___boxed(lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_Grind_isLegacyNormalizer(v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_symNorm(lean_object* v_e_39_, lean_object* v_methods_40_, lean_object* v_dmethods_41_, lean_object* v_s_42_, lean_object* v_ds_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Grind_foldProjs(v_e_39_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = l_Lean_Meta_Sym_preprocessExpr(v_a_52_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_n(v_a_54_, 2);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_55_, 0, v_a_54_);
v___x_56_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__0));
v___x_57_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_55_, v_methods_40_, v___x_56_, v_s_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_104_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_104_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_104_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_104_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_103_; 
v_fst_62_ = lean_ctor_get(v_a_58_, 0);
v_snd_63_ = lean_ctor_get(v_a_58_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_a_58_);
if (v_isSharedCheck_103_ == 0)
{
v___x_65_ = v_a_58_;
v_isShared_66_ = v_isSharedCheck_103_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_a_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_103_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v___y_70_; lean_object* v_fst_81_; lean_object* v_snd_82_; 
if (lean_obj_tag(v_fst_62_) == 0)
{
lean_object* v___x_99_; 
lean_dec_ref_known(v_fst_62_, 0);
v___x_99_ = lean_box(0);
v_fst_81_ = v_a_54_;
v_snd_82_ = v___x_99_;
goto v___jp_80_;
}
else
{
lean_object* v_e_x27_100_; lean_object* v_proof_101_; lean_object* v___x_102_; 
lean_dec(v_a_54_);
v_e_x27_100_ = lean_ctor_get(v_fst_62_, 0);
lean_inc_ref(v_e_x27_100_);
v_proof_101_ = lean_ctor_get(v_fst_62_, 1);
lean_inc_ref(v_proof_101_);
lean_dec_ref_known(v_fst_62_, 2);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_proof_101_);
v_fst_81_ = v_e_x27_100_;
v_snd_82_ = v___x_102_;
goto v___jp_80_;
}
v___jp_67_:
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_71_ = 1;
v___x_72_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_72_, 0, v___y_70_);
lean_ctor_set(v___x_72_, 1, v___y_69_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2, v___x_71_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___y_68_);
lean_ctor_set(v___x_65_, 0, v_snd_63_);
v___x_74_ = v___x_65_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_snd_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___y_68_);
v___x_74_ = v_reuseFailAlloc_79_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_75_);
v___x_77_ = v___x_60_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
v___jp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc_ref(v_fst_81_);
v___x_83_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_83_, 0, v_fst_81_);
v___x_84_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
v___x_85_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_83_, v_dmethods_41_, v___x_84_, v_ds_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v_fst_87_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_85_, 1);
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
if (lean_obj_tag(v_fst_87_) == 0)
{
lean_object* v_snd_88_; 
v_snd_88_ = lean_ctor_get(v_a_86_, 1);
lean_inc(v_snd_88_);
lean_dec(v_a_86_);
v___y_68_ = v_snd_88_;
v___y_69_ = v_snd_82_;
v___y_70_ = v_fst_81_;
goto v___jp_67_;
}
else
{
lean_object* v_snd_89_; lean_object* v_e_x27_90_; 
lean_inc_ref(v_fst_87_);
lean_dec_ref(v_fst_81_);
v_snd_89_ = lean_ctor_get(v_a_86_, 1);
lean_inc(v_snd_89_);
lean_dec(v_a_86_);
v_e_x27_90_ = lean_ctor_get(v_fst_87_, 0);
lean_inc_ref(v_e_x27_90_);
lean_dec_ref_known(v_fst_87_, 1);
v___y_68_ = v_snd_89_;
v___y_69_ = v_snd_82_;
v___y_70_ = v_e_x27_90_;
goto v___jp_67_;
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_snd_82_);
lean_dec_ref(v_fst_81_);
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_del_object(v___x_60_);
v_a_91_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_85_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_85_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v_a_54_);
lean_dec_ref(v_ds_43_);
lean_dec_ref(v_dmethods_41_);
v_a_105_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_57_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_57_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec_ref(v_ds_43_);
lean_dec_ref(v_s_42_);
lean_dec_ref(v_dmethods_41_);
lean_dec_ref(v_methods_40_);
v_a_113_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_53_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_53_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v_ds_43_);
lean_dec_ref(v_s_42_);
lean_dec_ref(v_dmethods_41_);
lean_dec_ref(v_methods_40_);
v_a_121_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_51_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_51_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_symNorm___boxed(lean_object* v_e_129_, lean_object* v_methods_130_, lean_object* v_dmethods_131_, lean_object* v_s_132_, lean_object* v_ds_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_symNorm(v_e_129_, v_methods_130_, v_dmethods_131_, v_s_132_, v_ds_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(lean_object* v_category_142_, lean_object* v_opts_143_, lean_object* v_act_144_, lean_object* v_decl_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
v___x_156_ = lean_apply_9(v_act_144_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v___x_157_ = l_Lean_profileitIOUnsafe___redArg(v_category_142_, v_opts_143_, v___x_156_, v_decl_145_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg___boxed(lean_object* v_category_158_, lean_object* v_opts_159_, lean_object* v_act_160_, lean_object* v_decl_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v_category_158_, v_opts_159_, v_act_160_, v_decl_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v_opts_159_);
lean_dec_ref(v_category_158_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(lean_object* v_00_u03b1_173_, lean_object* v_category_174_, lean_object* v_opts_175_, lean_object* v_act_176_, lean_object* v_decl_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v_category_174_, v_opts_175_, v_act_176_, v_decl_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___boxed(lean_object* v_00_u03b1_189_, lean_object* v_category_190_, lean_object* v_opts_191_, lean_object* v_act_192_, lean_object* v_decl_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(v_00_u03b1_189_, v_category_190_, v_opts_191_, v_act_192_, v_decl_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v_opts_191_);
lean_dec_ref(v_category_190_);
return v_res_204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_208_);
lean_ctor_set(v___x_210_, 3, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(lean_object* v_e_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v_congrThms_226_; lean_object* v_simp_227_; lean_object* v_symSimp_228_; lean_object* v_symDSimp_229_; lean_object* v_lastTag_230_; lean_object* v_counters_231_; lean_object* v_splitDiags_232_; lean_object* v_ematchDiags_233_; lean_object* v_lawfulEqCmpMap_234_; lean_object* v_reflCmpMap_235_; lean_object* v_anchors_236_; lean_object* v_instanceMap_237_; lean_object* v_hoistedDecls_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_293_; 
v___x_225_ = lean_st_ref_take(v___y_217_);
v_congrThms_226_ = lean_ctor_get(v___x_225_, 0);
v_simp_227_ = lean_ctor_get(v___x_225_, 1);
v_symSimp_228_ = lean_ctor_get(v___x_225_, 2);
v_symDSimp_229_ = lean_ctor_get(v___x_225_, 3);
v_lastTag_230_ = lean_ctor_get(v___x_225_, 4);
v_counters_231_ = lean_ctor_get(v___x_225_, 5);
v_splitDiags_232_ = lean_ctor_get(v___x_225_, 6);
v_ematchDiags_233_ = lean_ctor_get(v___x_225_, 7);
v_lawfulEqCmpMap_234_ = lean_ctor_get(v___x_225_, 8);
v_reflCmpMap_235_ = lean_ctor_get(v___x_225_, 9);
v_anchors_236_ = lean_ctor_get(v___x_225_, 10);
v_instanceMap_237_ = lean_ctor_get(v___x_225_, 11);
v_hoistedDecls_238_ = lean_ctor_get(v___x_225_, 12);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_293_ == 0)
{
v___x_240_ = v___x_225_;
v_isShared_241_ = v_isSharedCheck_293_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_hoistedDecls_238_);
lean_inc(v_instanceMap_237_);
lean_inc(v_anchors_236_);
lean_inc(v_reflCmpMap_235_);
lean_inc(v_lawfulEqCmpMap_234_);
lean_inc(v_ematchDiags_233_);
lean_inc(v_splitDiags_232_);
lean_inc(v_counters_231_);
lean_inc(v_lastTag_230_);
lean_inc(v_symDSimp_229_);
lean_inc(v_symSimp_228_);
lean_inc(v_simp_227_);
lean_inc(v_congrThms_226_);
lean_dec(v___x_225_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_293_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2);
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v___x_243_);
lean_ctor_set(v___x_240_, 2, v___x_242_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_congrThms_226_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_simp_227_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_lastTag_230_);
lean_ctor_set(v_reuseFailAlloc_292_, 5, v_counters_231_);
lean_ctor_set(v_reuseFailAlloc_292_, 6, v_splitDiags_232_);
lean_ctor_set(v_reuseFailAlloc_292_, 7, v_ematchDiags_233_);
lean_ctor_set(v_reuseFailAlloc_292_, 8, v_lawfulEqCmpMap_234_);
lean_ctor_set(v_reuseFailAlloc_292_, 9, v_reflCmpMap_235_);
lean_ctor_set(v_reuseFailAlloc_292_, 10, v_anchors_236_);
lean_ctor_set(v_reuseFailAlloc_292_, 11, v_instanceMap_237_);
lean_ctor_set(v_reuseFailAlloc_292_, 12, v_hoistedDecls_238_);
v___x_245_ = v_reuseFailAlloc_292_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v_symSimpMethods_247_; lean_object* v_symDSimpMethods_248_; lean_object* v___x_249_; 
v___x_246_ = lean_st_ref_put(v___y_217_, v___x_245_);
v_symSimpMethods_247_ = lean_ctor_get(v___y_216_, 2);
v_symDSimpMethods_248_ = lean_ctor_get(v___y_216_, 3);
lean_inc_ref(v_symDSimpMethods_248_);
lean_inc_ref(v_symSimpMethods_247_);
v___x_249_ = l_Lean_Meta_Grind_symNorm(v_e_214_, v_symSimpMethods_247_, v_symDSimpMethods_248_, v_symSimp_228_, v_symDSimp_229_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_283_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_283_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_283_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_283_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_snd_254_; lean_object* v_fst_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v___x_258_; lean_object* v_congrThms_259_; lean_object* v_simp_260_; lean_object* v_lastTag_261_; lean_object* v_counters_262_; lean_object* v_splitDiags_263_; lean_object* v_ematchDiags_264_; lean_object* v_lawfulEqCmpMap_265_; lean_object* v_reflCmpMap_266_; lean_object* v_anchors_267_; lean_object* v_instanceMap_268_; lean_object* v_hoistedDecls_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
v_snd_254_ = lean_ctor_get(v_a_250_, 1);
lean_inc(v_snd_254_);
v_fst_255_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_fst_255_);
lean_dec(v_a_250_);
v_fst_256_ = lean_ctor_get(v_snd_254_, 0);
lean_inc(v_fst_256_);
v_snd_257_ = lean_ctor_get(v_snd_254_, 1);
lean_inc(v_snd_257_);
lean_dec(v_snd_254_);
v___x_258_ = lean_st_ref_take(v___y_217_);
v_congrThms_259_ = lean_ctor_get(v___x_258_, 0);
v_simp_260_ = lean_ctor_get(v___x_258_, 1);
v_lastTag_261_ = lean_ctor_get(v___x_258_, 4);
v_counters_262_ = lean_ctor_get(v___x_258_, 5);
v_splitDiags_263_ = lean_ctor_get(v___x_258_, 6);
v_ematchDiags_264_ = lean_ctor_get(v___x_258_, 7);
v_lawfulEqCmpMap_265_ = lean_ctor_get(v___x_258_, 8);
v_reflCmpMap_266_ = lean_ctor_get(v___x_258_, 9);
v_anchors_267_ = lean_ctor_get(v___x_258_, 10);
v_instanceMap_268_ = lean_ctor_get(v___x_258_, 11);
v_hoistedDecls_269_ = lean_ctor_get(v___x_258_, 12);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; 
v_unused_281_ = lean_ctor_get(v___x_258_, 3);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v___x_258_, 2);
lean_dec(v_unused_282_);
v___x_271_ = v___x_258_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_hoistedDecls_269_);
lean_inc(v_instanceMap_268_);
lean_inc(v_anchors_267_);
lean_inc(v_reflCmpMap_266_);
lean_inc(v_lawfulEqCmpMap_265_);
lean_inc(v_ematchDiags_264_);
lean_inc(v_splitDiags_263_);
lean_inc(v_counters_262_);
lean_inc(v_lastTag_261_);
lean_inc(v_simp_260_);
lean_inc(v_congrThms_259_);
lean_dec(v___x_258_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 3, v_snd_257_);
lean_ctor_set(v___x_271_, 2, v_fst_256_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_congrThms_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_simp_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_fst_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_snd_257_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_lastTag_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_counters_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_splitDiags_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_ematchDiags_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_lawfulEqCmpMap_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v_reflCmpMap_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 10, v_anchors_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 11, v_instanceMap_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 12, v_hoistedDecls_269_);
v___x_274_ = v_reuseFailAlloc_279_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_st_ref_put(v___y_217_, v___x_274_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_fst_255_);
v___x_277_ = v___x_252_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_fst_255_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_249_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_249_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed(lean_object* v_e_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(v_e_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___f_318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_318_, 0, v_e_307_);
v___x_319_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_315_);
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_321_ = lean_box(0);
v___x_322_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_320_, v___x_319_, v___f_318_, v___x_321_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec_ref(v___x_319_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___boxed(lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(lean_object* v_e_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_Grind_foldProjs(v_e_340_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l_Lean_Meta_Sym_preprocessExpr(v_a_352_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; lean_object* v_congrThms_356_; lean_object* v_simp_357_; lean_object* v_symSimp_358_; lean_object* v_symDSimp_359_; lean_object* v_lastTag_360_; lean_object* v_counters_361_; lean_object* v_splitDiags_362_; lean_object* v_ematchDiags_363_; lean_object* v_lawfulEqCmpMap_364_; lean_object* v_reflCmpMap_365_; lean_object* v_anchors_366_; lean_object* v_instanceMap_367_; lean_object* v_hoistedDecls_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_425_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_355_ = lean_st_ref_take(v___y_343_);
v_congrThms_356_ = lean_ctor_get(v___x_355_, 0);
v_simp_357_ = lean_ctor_get(v___x_355_, 1);
v_symSimp_358_ = lean_ctor_get(v___x_355_, 2);
v_symDSimp_359_ = lean_ctor_get(v___x_355_, 3);
v_lastTag_360_ = lean_ctor_get(v___x_355_, 4);
v_counters_361_ = lean_ctor_get(v___x_355_, 5);
v_splitDiags_362_ = lean_ctor_get(v___x_355_, 6);
v_ematchDiags_363_ = lean_ctor_get(v___x_355_, 7);
v_lawfulEqCmpMap_364_ = lean_ctor_get(v___x_355_, 8);
v_reflCmpMap_365_ = lean_ctor_get(v___x_355_, 9);
v_anchors_366_ = lean_ctor_get(v___x_355_, 10);
v_instanceMap_367_ = lean_ctor_get(v___x_355_, 11);
v_hoistedDecls_368_ = lean_ctor_get(v___x_355_, 12);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_425_ == 0)
{
v___x_370_ = v___x_355_;
v_isShared_371_ = v_isSharedCheck_425_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_hoistedDecls_368_);
lean_inc(v_instanceMap_367_);
lean_inc(v_anchors_366_);
lean_inc(v_reflCmpMap_365_);
lean_inc(v_lawfulEqCmpMap_364_);
lean_inc(v_ematchDiags_363_);
lean_inc(v_splitDiags_362_);
lean_inc(v_counters_361_);
lean_inc(v_lastTag_360_);
lean_inc(v_symDSimp_359_);
lean_inc(v_symSimp_358_);
lean_inc(v_simp_357_);
lean_inc(v_congrThms_356_);
lean_dec(v___x_355_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_425_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 3, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_congrThms_356_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_simp_357_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_symSimp_358_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_lastTag_360_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_counters_361_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_splitDiags_362_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_ematchDiags_363_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_lawfulEqCmpMap_364_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_reflCmpMap_365_);
lean_ctor_set(v_reuseFailAlloc_424_, 10, v_anchors_366_);
lean_ctor_set(v_reuseFailAlloc_424_, 11, v_instanceMap_367_);
lean_ctor_set(v_reuseFailAlloc_424_, 12, v_hoistedDecls_368_);
v___x_374_ = v_reuseFailAlloc_424_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v_symDSimpMethods_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = lean_st_ref_put(v___y_343_, v___x_374_);
v_symDSimpMethods_376_ = lean_ctor_get(v___y_342_, 3);
lean_inc(v_a_354_);
v___x_377_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_377_, 0, v_a_354_);
v___x_378_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
lean_inc_ref(v_symDSimpMethods_376_);
v___x_379_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_377_, v_symDSimpMethods_376_, v___x_378_, v_symDSimp_359_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_415_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_415_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_415_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_415_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_386_; lean_object* v_congrThms_387_; lean_object* v_simp_388_; lean_object* v_symSimp_389_; lean_object* v_lastTag_390_; lean_object* v_counters_391_; lean_object* v_splitDiags_392_; lean_object* v_ematchDiags_393_; lean_object* v_lawfulEqCmpMap_394_; lean_object* v_reflCmpMap_395_; lean_object* v_anchors_396_; lean_object* v_instanceMap_397_; lean_object* v_hoistedDecls_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_413_; 
v_fst_384_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v_a_380_, 1);
lean_inc(v_snd_385_);
lean_dec(v_a_380_);
v___x_386_ = lean_st_ref_take(v___y_343_);
v_congrThms_387_ = lean_ctor_get(v___x_386_, 0);
v_simp_388_ = lean_ctor_get(v___x_386_, 1);
v_symSimp_389_ = lean_ctor_get(v___x_386_, 2);
v_lastTag_390_ = lean_ctor_get(v___x_386_, 4);
v_counters_391_ = lean_ctor_get(v___x_386_, 5);
v_splitDiags_392_ = lean_ctor_get(v___x_386_, 6);
v_ematchDiags_393_ = lean_ctor_get(v___x_386_, 7);
v_lawfulEqCmpMap_394_ = lean_ctor_get(v___x_386_, 8);
v_reflCmpMap_395_ = lean_ctor_get(v___x_386_, 9);
v_anchors_396_ = lean_ctor_get(v___x_386_, 10);
v_instanceMap_397_ = lean_ctor_get(v___x_386_, 11);
v_hoistedDecls_398_ = lean_ctor_get(v___x_386_, 12);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_386_, 3);
lean_dec(v_unused_414_);
v___x_400_ = v___x_386_;
v_isShared_401_ = v_isSharedCheck_413_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_hoistedDecls_398_);
lean_inc(v_instanceMap_397_);
lean_inc(v_anchors_396_);
lean_inc(v_reflCmpMap_395_);
lean_inc(v_lawfulEqCmpMap_394_);
lean_inc(v_ematchDiags_393_);
lean_inc(v_splitDiags_392_);
lean_inc(v_counters_391_);
lean_inc(v_lastTag_390_);
lean_inc(v_symSimp_389_);
lean_inc(v_simp_388_);
lean_inc(v_congrThms_387_);
lean_dec(v___x_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_413_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 3, v_snd_385_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_congrThms_387_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_simp_388_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_symSimp_389_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_snd_385_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_lastTag_390_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_counters_391_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_splitDiags_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_ematchDiags_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_lawfulEqCmpMap_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 9, v_reflCmpMap_395_);
lean_ctor_set(v_reuseFailAlloc_412_, 10, v_anchors_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 11, v_instanceMap_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 12, v_hoistedDecls_398_);
v___x_403_ = v_reuseFailAlloc_412_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_st_ref_put(v___y_343_, v___x_403_);
if (lean_obj_tag(v_fst_384_) == 0)
{
lean_object* v___x_406_; 
lean_dec_ref_known(v_fst_384_, 0);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_a_354_);
v___x_406_ = v___x_382_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_354_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v_e_x27_408_; lean_object* v___x_410_; 
lean_dec(v_a_354_);
v_e_x27_408_ = lean_ctor_get(v_fst_384_, 0);
lean_inc_ref(v_e_x27_408_);
lean_dec_ref_known(v_fst_384_, 1);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_e_x27_408_);
v___x_410_ = v___x_382_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_e_x27_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_a_354_);
v_a_416_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_379_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_379_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
else
{
return v___x_353_;
}
}
else
{
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed(lean_object* v_e_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(v_e_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___f_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___f_450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_450_, 0, v_e_439_);
v___x_451_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_447_);
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_453_ = lean_box(0);
v___x_454_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_452_, v___x_451_, v___f_450_, v___x_453_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec_ref(v___x_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___boxed(lean_object* v_e_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
return v_res_466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_box(0);
v___x_468_ = lean_unsigned_to_nat(16u);
v___x_469_ = lean_mk_array(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; 
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_477_ = 1;
v___x_478_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_475_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*2, v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(32u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6(void){
_start:
{
size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = ((size_t)5ULL);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_unsigned_to_nat(32u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5);
v___x_490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_486_);
lean_ctor_set(v___x_490_, 3, v___x_486_);
lean_ctor_set_usize(v___x_490_, 4, v___x_485_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6);
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_493_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
lean_ctor_set(v___x_493_, 2, v___x_492_);
lean_ctor_set(v___x_493_, 3, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4);
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3);
v___x_499_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_497_);
lean_ctor_set(v___x_499_, 3, v___x_496_);
lean_ctor_set(v___x_499_, 4, v___x_495_);
lean_ctor_set(v___x_499_, 5, v___x_494_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(lean_object* v_e_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; lean_object* v_congrThms_512_; lean_object* v_simp_513_; lean_object* v_symSimp_514_; lean_object* v_symDSimp_515_; lean_object* v_lastTag_516_; lean_object* v_counters_517_; lean_object* v_splitDiags_518_; lean_object* v_ematchDiags_519_; lean_object* v_lawfulEqCmpMap_520_; lean_object* v_reflCmpMap_521_; lean_object* v_anchors_522_; lean_object* v_instanceMap_523_; lean_object* v_hoistedDecls_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_576_; 
v___x_511_ = lean_st_ref_take(v___y_503_);
v_congrThms_512_ = lean_ctor_get(v___x_511_, 0);
v_simp_513_ = lean_ctor_get(v___x_511_, 1);
v_symSimp_514_ = lean_ctor_get(v___x_511_, 2);
v_symDSimp_515_ = lean_ctor_get(v___x_511_, 3);
v_lastTag_516_ = lean_ctor_get(v___x_511_, 4);
v_counters_517_ = lean_ctor_get(v___x_511_, 5);
v_splitDiags_518_ = lean_ctor_get(v___x_511_, 6);
v_ematchDiags_519_ = lean_ctor_get(v___x_511_, 7);
v_lawfulEqCmpMap_520_ = lean_ctor_get(v___x_511_, 8);
v_reflCmpMap_521_ = lean_ctor_get(v___x_511_, 9);
v_anchors_522_ = lean_ctor_get(v___x_511_, 10);
v_instanceMap_523_ = lean_ctor_get(v___x_511_, 11);
v_hoistedDecls_524_ = lean_ctor_get(v___x_511_, 12);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_576_ == 0)
{
v___x_526_ = v___x_511_;
v_isShared_527_ = v_isSharedCheck_576_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_hoistedDecls_524_);
lean_inc(v_instanceMap_523_);
lean_inc(v_anchors_522_);
lean_inc(v_reflCmpMap_521_);
lean_inc(v_lawfulEqCmpMap_520_);
lean_inc(v_ematchDiags_519_);
lean_inc(v_splitDiags_518_);
lean_inc(v_counters_517_);
lean_inc(v_lastTag_516_);
lean_inc(v_symDSimp_515_);
lean_inc(v_symSimp_514_);
lean_inc(v_simp_513_);
lean_inc(v_congrThms_512_);
lean_dec(v___x_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_576_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_congrThms_512_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_symSimp_514_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_symDSimp_515_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_lastTag_516_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v_counters_517_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_splitDiags_518_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_ematchDiags_519_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_lawfulEqCmpMap_520_);
lean_ctor_set(v_reuseFailAlloc_575_, 9, v_reflCmpMap_521_);
lean_ctor_set(v_reuseFailAlloc_575_, 10, v_anchors_522_);
lean_ctor_set(v_reuseFailAlloc_575_, 11, v_instanceMap_523_);
lean_ctor_set(v_reuseFailAlloc_575_, 12, v_hoistedDecls_524_);
v___x_530_ = v_reuseFailAlloc_575_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v_simp_532_; lean_object* v_simpMethods_533_; lean_object* v___x_534_; 
v___x_531_ = lean_st_ref_put(v___y_503_, v___x_530_);
v_simp_532_ = lean_ctor_get(v___y_502_, 0);
v_simpMethods_533_ = lean_ctor_get(v___y_502_, 1);
lean_inc_ref(v_simpMethods_533_);
lean_inc_ref(v_simp_532_);
v___x_534_ = l_Lean_Meta_Simp_mainCore(v_e_500_, v_simp_532_, v_simp_513_, v_simpMethods_533_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_566_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_566_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_566_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_566_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; lean_object* v_congrThms_542_; lean_object* v_symSimp_543_; lean_object* v_symDSimp_544_; lean_object* v_lastTag_545_; lean_object* v_counters_546_; lean_object* v_splitDiags_547_; lean_object* v_ematchDiags_548_; lean_object* v_lawfulEqCmpMap_549_; lean_object* v_reflCmpMap_550_; lean_object* v_anchors_551_; lean_object* v_instanceMap_552_; lean_object* v_hoistedDecls_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_564_; 
v_fst_539_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v_a_535_, 1);
lean_inc(v_snd_540_);
lean_dec(v_a_535_);
v___x_541_ = lean_st_ref_take(v___y_503_);
v_congrThms_542_ = lean_ctor_get(v___x_541_, 0);
v_symSimp_543_ = lean_ctor_get(v___x_541_, 2);
v_symDSimp_544_ = lean_ctor_get(v___x_541_, 3);
v_lastTag_545_ = lean_ctor_get(v___x_541_, 4);
v_counters_546_ = lean_ctor_get(v___x_541_, 5);
v_splitDiags_547_ = lean_ctor_get(v___x_541_, 6);
v_ematchDiags_548_ = lean_ctor_get(v___x_541_, 7);
v_lawfulEqCmpMap_549_ = lean_ctor_get(v___x_541_, 8);
v_reflCmpMap_550_ = lean_ctor_get(v___x_541_, 9);
v_anchors_551_ = lean_ctor_get(v___x_541_, 10);
v_instanceMap_552_ = lean_ctor_get(v___x_541_, 11);
v_hoistedDecls_553_ = lean_ctor_get(v___x_541_, 12);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_541_, 1);
lean_dec(v_unused_565_);
v___x_555_ = v___x_541_;
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_hoistedDecls_553_);
lean_inc(v_instanceMap_552_);
lean_inc(v_anchors_551_);
lean_inc(v_reflCmpMap_550_);
lean_inc(v_lawfulEqCmpMap_549_);
lean_inc(v_ematchDiags_548_);
lean_inc(v_splitDiags_547_);
lean_inc(v_counters_546_);
lean_inc(v_lastTag_545_);
lean_inc(v_symDSimp_544_);
lean_inc(v_symSimp_543_);
lean_inc(v_congrThms_542_);
lean_dec(v___x_541_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_snd_540_);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_congrThms_542_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_snd_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_symSimp_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_symDSimp_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_lastTag_545_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_counters_546_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_splitDiags_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_ematchDiags_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_lawfulEqCmpMap_549_);
lean_ctor_set(v_reuseFailAlloc_563_, 9, v_reflCmpMap_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 10, v_anchors_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 11, v_instanceMap_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 12, v_hoistedDecls_553_);
v___x_558_ = v_reuseFailAlloc_563_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_st_ref_put(v___y_503_, v___x_558_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_fst_539_);
v___x_561_ = v___x_537_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fst_539_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_534_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_534_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed(lean_object* v_e_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(v_e_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___f_600_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_600_, 0, v_e_589_);
v___x_601_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_597_);
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_603_ = lean_box(0);
v___x_604_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_602_, v___x_601_, v___f_600_, v___x_603_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec_ref(v___x_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___boxed(lean_object* v_e_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(lean_object* v_e_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_congrThms_629_; lean_object* v_simp_630_; lean_object* v_symSimp_631_; lean_object* v_symDSimp_632_; lean_object* v_lastTag_633_; lean_object* v_counters_634_; lean_object* v_splitDiags_635_; lean_object* v_ematchDiags_636_; lean_object* v_lawfulEqCmpMap_637_; lean_object* v_reflCmpMap_638_; lean_object* v_anchors_639_; lean_object* v_instanceMap_640_; lean_object* v_hoistedDecls_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_695_; 
v___x_628_ = lean_st_ref_take(v___y_620_);
v_congrThms_629_ = lean_ctor_get(v___x_628_, 0);
v_simp_630_ = lean_ctor_get(v___x_628_, 1);
v_symSimp_631_ = lean_ctor_get(v___x_628_, 2);
v_symDSimp_632_ = lean_ctor_get(v___x_628_, 3);
v_lastTag_633_ = lean_ctor_get(v___x_628_, 4);
v_counters_634_ = lean_ctor_get(v___x_628_, 5);
v_splitDiags_635_ = lean_ctor_get(v___x_628_, 6);
v_ematchDiags_636_ = lean_ctor_get(v___x_628_, 7);
v_lawfulEqCmpMap_637_ = lean_ctor_get(v___x_628_, 8);
v_reflCmpMap_638_ = lean_ctor_get(v___x_628_, 9);
v_anchors_639_ = lean_ctor_get(v___x_628_, 10);
v_instanceMap_640_ = lean_ctor_get(v___x_628_, 11);
v_hoistedDecls_641_ = lean_ctor_get(v___x_628_, 12);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_695_ == 0)
{
v___x_643_ = v___x_628_;
v_isShared_644_ = v_isSharedCheck_695_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_hoistedDecls_641_);
lean_inc(v_instanceMap_640_);
lean_inc(v_anchors_639_);
lean_inc(v_reflCmpMap_638_);
lean_inc(v_lawfulEqCmpMap_637_);
lean_inc(v_ematchDiags_636_);
lean_inc(v_splitDiags_635_);
lean_inc(v_counters_634_);
lean_inc(v_lastTag_633_);
lean_inc(v_symDSimp_632_);
lean_inc(v_symSimp_631_);
lean_inc(v_simp_630_);
lean_inc(v_congrThms_629_);
lean_dec(v___x_628_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_695_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_645_ = lean_unsigned_to_nat(32u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
lean_dec_ref(v___x_646_);
v___x_647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_647_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_congrThms_629_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_symSimp_631_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_symDSimp_632_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_lastTag_633_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_counters_634_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_splitDiags_635_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_ematchDiags_636_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_lawfulEqCmpMap_637_);
lean_ctor_set(v_reuseFailAlloc_694_, 9, v_reflCmpMap_638_);
lean_ctor_set(v_reuseFailAlloc_694_, 10, v_anchors_639_);
lean_ctor_set(v_reuseFailAlloc_694_, 11, v_instanceMap_640_);
lean_ctor_set(v_reuseFailAlloc_694_, 12, v_hoistedDecls_641_);
v___x_649_ = v_reuseFailAlloc_694_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v_simp_651_; lean_object* v_simpMethods_652_; lean_object* v___x_653_; 
v___x_650_ = lean_st_ref_put(v___y_620_, v___x_649_);
v_simp_651_ = lean_ctor_get(v___y_619_, 0);
v_simpMethods_652_ = lean_ctor_get(v___y_619_, 1);
lean_inc_ref(v_simpMethods_652_);
lean_inc_ref(v_simp_651_);
v___x_653_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_617_, v_simp_651_, v_simp_630_, v_simpMethods_652_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_685_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_685_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_660_; lean_object* v_congrThms_661_; lean_object* v_symSimp_662_; lean_object* v_symDSimp_663_; lean_object* v_lastTag_664_; lean_object* v_counters_665_; lean_object* v_splitDiags_666_; lean_object* v_ematchDiags_667_; lean_object* v_lawfulEqCmpMap_668_; lean_object* v_reflCmpMap_669_; lean_object* v_anchors_670_; lean_object* v_instanceMap_671_; lean_object* v_hoistedDecls_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_683_; 
v_fst_658_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v_a_654_, 1);
lean_inc(v_snd_659_);
lean_dec(v_a_654_);
v___x_660_ = lean_st_ref_take(v___y_620_);
v_congrThms_661_ = lean_ctor_get(v___x_660_, 0);
v_symSimp_662_ = lean_ctor_get(v___x_660_, 2);
v_symDSimp_663_ = lean_ctor_get(v___x_660_, 3);
v_lastTag_664_ = lean_ctor_get(v___x_660_, 4);
v_counters_665_ = lean_ctor_get(v___x_660_, 5);
v_splitDiags_666_ = lean_ctor_get(v___x_660_, 6);
v_ematchDiags_667_ = lean_ctor_get(v___x_660_, 7);
v_lawfulEqCmpMap_668_ = lean_ctor_get(v___x_660_, 8);
v_reflCmpMap_669_ = lean_ctor_get(v___x_660_, 9);
v_anchors_670_ = lean_ctor_get(v___x_660_, 10);
v_instanceMap_671_ = lean_ctor_get(v___x_660_, 11);
v_hoistedDecls_672_ = lean_ctor_get(v___x_660_, 12);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_660_, 1);
lean_dec(v_unused_684_);
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_hoistedDecls_672_);
lean_inc(v_instanceMap_671_);
lean_inc(v_anchors_670_);
lean_inc(v_reflCmpMap_669_);
lean_inc(v_lawfulEqCmpMap_668_);
lean_inc(v_ematchDiags_667_);
lean_inc(v_splitDiags_666_);
lean_inc(v_counters_665_);
lean_inc(v_lastTag_664_);
lean_inc(v_symDSimp_663_);
lean_inc(v_symSimp_662_);
lean_inc(v_congrThms_661_);
lean_dec(v___x_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_snd_659_);
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_congrThms_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_snd_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_symSimp_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_symDSimp_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_lastTag_664_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_counters_665_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_splitDiags_666_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_ematchDiags_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_lawfulEqCmpMap_668_);
lean_ctor_set(v_reuseFailAlloc_682_, 9, v_reflCmpMap_669_);
lean_ctor_set(v_reuseFailAlloc_682_, 10, v_anchors_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 11, v_instanceMap_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 12, v_hoistedDecls_672_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_st_ref_put(v___y_620_, v___x_677_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_fst_658_);
v___x_680_ = v___x_656_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_fst_658_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_653_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_653_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed(lean_object* v_e_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(v_e_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___f_719_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_719_, 0, v_e_708_);
v___x_720_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_716_);
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_722_ = lean_box(0);
v___x_723_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_721_, v___x_720_, v___f_719_, v___x_722_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec_ref(v___x_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v_a_748_; uint8_t v___x_749_; 
v___x_747_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v___x_749_ = lean_unbox(v_a_748_);
lean_dec(v_a_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_simpCore(v_e_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_a_776_; uint8_t v___x_777_; 
v___x_775_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_772_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = lean_unbox(v_a_776_);
lean_dec(v_a_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Grind_dsimpCore(v_e_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_792_, lean_object* v___y_793_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_Lean_Expr_hasMVar(v_e_792_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_e_792_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v_mctx_798_; lean_object* v___x_799_; lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_802_; lean_object* v_cache_803_; lean_object* v_zetaDeltaFVarIds_804_; lean_object* v_postponed_805_; lean_object* v_diag_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v___x_797_ = lean_st_ref_get(v___y_793_);
v_mctx_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_ref(v_mctx_798_);
lean_dec(v___x_797_);
v___x_799_ = l_Lean_instantiateMVarsCore(v_mctx_798_, v_e_792_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_fst_800_);
v_snd_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_snd_801_);
lean_dec_ref(v___x_799_);
v___x_802_ = lean_st_ref_take(v___y_793_);
v_cache_803_ = lean_ctor_get(v___x_802_, 1);
v_zetaDeltaFVarIds_804_ = lean_ctor_get(v___x_802_, 2);
v_postponed_805_ = lean_ctor_get(v___x_802_, 3);
v_diag_806_ = lean_ctor_get(v___x_802_, 4);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_816_);
v___x_808_ = v___x_802_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_diag_806_);
lean_inc(v_postponed_805_);
lean_inc(v_zetaDeltaFVarIds_804_);
lean_inc(v_cache_803_);
lean_dec(v___x_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_snd_801_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_snd_801_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_cache_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_zetaDeltaFVarIds_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_postponed_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_diag_806_);
v___x_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_st_ref_put(v___y_793_, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_fst_800_);
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_817_, v___y_818_);
lean_dec(v___y_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_821_, v___y_829_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v___y_835_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_env_854_; uint8_t v___x_855_; lean_object* v_env_856_; lean_object* v___x_857_; lean_object* v_toCold_858_; lean_object* v_mctx_859_; lean_object* v_lctx_860_; lean_object* v_options_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_853_ = lean_st_ref_get(v___y_851_);
v_env_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_env_854_);
lean_dec(v___x_853_);
v___x_855_ = 0;
v_env_856_ = l_Lean_Environment_setRecordingDeps(v_env_854_, v___x_855_);
v___x_857_ = lean_st_ref_get(v___y_849_);
v_toCold_858_ = lean_ctor_get(v___y_850_, 0);
v_mctx_859_ = lean_ctor_get(v___x_857_, 0);
lean_inc_ref(v_mctx_859_);
lean_dec(v___x_857_);
v_lctx_860_ = lean_ctor_get(v___y_848_, 2);
v_options_861_ = lean_ctor_get(v_toCold_858_, 2);
lean_inc_ref(v_options_861_);
lean_inc_ref(v_lctx_860_);
v___x_862_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_862_, 0, v_env_856_);
lean_ctor_set(v___x_862_, 1, v_mctx_859_);
lean_ctor_set(v___x_862_, 2, v_lctx_860_);
lean_ctor_set(v___x_862_, 3, v_options_861_);
v___x_863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_msgData_847_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_872_; double v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_float_of_nat(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_ref_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_931_; 
v_ref_884_ = lean_ctor_get(v___y_881_, 2);
v___x_885_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_931_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_931_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_931_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v_traceState_891_; lean_object* v_env_892_; lean_object* v_nextMacroScope_893_; lean_object* v_ngen_894_; lean_object* v_auxDeclNGen_895_; lean_object* v_cache_896_; lean_object* v_recordedDeps_897_; lean_object* v_messages_898_; lean_object* v_infoState_899_; lean_object* v_snapshotTasks_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_930_; 
v___x_890_ = lean_st_ref_take(v___y_882_);
v_traceState_891_ = lean_ctor_get(v___x_890_, 4);
v_env_892_ = lean_ctor_get(v___x_890_, 0);
v_nextMacroScope_893_ = lean_ctor_get(v___x_890_, 1);
v_ngen_894_ = lean_ctor_get(v___x_890_, 2);
v_auxDeclNGen_895_ = lean_ctor_get(v___x_890_, 3);
v_cache_896_ = lean_ctor_get(v___x_890_, 5);
v_recordedDeps_897_ = lean_ctor_get(v___x_890_, 6);
v_messages_898_ = lean_ctor_get(v___x_890_, 7);
v_infoState_899_ = lean_ctor_get(v___x_890_, 8);
v_snapshotTasks_900_ = lean_ctor_get(v___x_890_, 9);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_930_ == 0)
{
v___x_902_ = v___x_890_;
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snapshotTasks_900_);
lean_inc(v_infoState_899_);
lean_inc(v_messages_898_);
lean_inc(v_recordedDeps_897_);
lean_inc(v_cache_896_);
lean_inc(v_traceState_891_);
lean_inc(v_auxDeclNGen_895_);
lean_inc(v_ngen_894_);
lean_inc(v_nextMacroScope_893_);
lean_inc(v_env_892_);
lean_dec(v___x_890_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint64_t v_tid_904_; lean_object* v_traces_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_929_; 
v_tid_904_ = lean_ctor_get_uint64(v_traceState_891_, sizeof(void*)*1);
v_traces_905_ = lean_ctor_get(v_traceState_891_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_traceState_891_);
if (v_isSharedCheck_929_ == 0)
{
v___x_907_ = v_traceState_891_;
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_traces_905_);
lean_dec(v_traceState_891_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; double v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_909_ = lean_box(0);
v___x_910_ = lean_box(0);
v___x_911_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_912_ = 0;
v___x_913_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_914_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_914_, 0, v_cls_877_);
lean_ctor_set(v___x_914_, 1, v___x_910_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
lean_ctor_set_float(v___x_914_, sizeof(void*)*3, v___x_911_);
lean_ctor_set_float(v___x_914_, sizeof(void*)*3 + 8, v___x_911_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*3 + 16, v___x_912_);
v___x_915_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_916_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v_a_886_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
lean_inc(v_ref_884_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_ref_884_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_PersistentArray_push___redArg(v_traces_905_, v___x_917_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_918_);
v___x_920_ = v___x_907_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_918_);
lean_ctor_set_uint64(v_reuseFailAlloc_928_, sizeof(void*)*1, v_tid_904_);
v___x_920_ = v_reuseFailAlloc_928_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_920_);
v___x_922_ = v___x_902_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_env_892_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_nextMacroScope_893_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_ngen_894_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_auxDeclNGen_895_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_cache_896_);
lean_ctor_set(v_reuseFailAlloc_927_, 6, v_recordedDeps_897_);
lean_ctor_set(v_reuseFailAlloc_927_, 7, v_messages_898_);
lean_ctor_set(v_reuseFailAlloc_927_, 8, v_infoState_899_);
lean_ctor_set(v_reuseFailAlloc_927_, 9, v_snapshotTasks_900_);
v___x_922_ = v_reuseFailAlloc_927_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_st_ref_put(v___y_882_, v___x_922_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_909_);
v___x_925_ = v___x_888_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_909_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_932_, lean_object* v_msg_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_932_, v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_949_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_950_ = l_Lean_Name_append(v___x_949_, v___x_948_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_954_, v_a_962_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_n(v_a_967_, 2);
lean_dec_ref(v___x_966_);
v___x_968_ = l_Lean_Meta_Grind_simpCore(v_a_967_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v_expr_970_; lean_object* v___x_971_; lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v_expr_970_ = lean_ctor_get(v_a_969_, 0);
lean_inc_ref(v_expr_970_);
v___x_971_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_970_, v_a_962_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Meta_Sym_unfoldReducible(v_a_972_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_974_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_976_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_978_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_Meta_Grind_foldProjs(v_a_980_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_Meta_Sym_normalizeLevels(v_a_982_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_984_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_n(v_a_986_, 2);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_969_, v_a_986_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_expr_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_expr_989_ = lean_ctor_get(v_a_986_, 0);
lean_inc_ref(v_expr_989_);
lean_dec(v_a_986_);
v___x_990_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_989_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_n(v_a_991_, 2);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_988_, v_a_991_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_expr_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v_expr_994_ = lean_ctor_get(v_a_991_, 0);
lean_inc_ref(v_expr_994_);
lean_dec(v_a_991_);
v___x_995_ = l_Lean_Meta_Sym_canon(v_expr_994_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = l_Lean_Meta_Sym_shareCommon(v_a_996_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1046_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1046_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1046_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_toCold_1016_; lean_object* v_options_1017_; uint8_t v_hasTrace_1018_; 
v_toCold_1016_ = lean_ctor_get(v_a_963_, 0);
v_options_1017_ = lean_ctor_get(v_toCold_1016_, 2);
v_hasTrace_1018_ = lean_ctor_get_uint8(v_options_1017_, sizeof(void*)*1);
if (v_hasTrace_1018_ == 0)
{
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
goto v___jp_1002_;
}
else
{
lean_object* v_inheritedTraceOptions_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_inheritedTraceOptions_1019_ = lean_ctor_get(v_toCold_1016_, 11);
v___x_1020_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_1021_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_1022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1019_, v_options_1017_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_Grind_updateLastTag(v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___x_1023_, 1);
v___x_1024_ = l_Lean_MessageData_ofExpr(v_a_967_);
v___x_1025_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
lean_inc(v_a_998_);
v___x_1027_ = l_Lean_MessageData_ofExpr(v_a_998_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1020_, v___x_1028_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref_known(v___x_1029_, 1);
goto v___jp_1002_;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1000_);
lean_dec(v_a_998_);
lean_dec(v_a_993_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_del_object(v___x_1000_);
lean_dec(v_a_998_);
lean_dec(v_a_993_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
v_a_1038_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1023_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1023_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
v___jp_1002_:
{
lean_object* v_proof_x3f_1003_; uint8_t v_cache_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1014_; 
v_proof_x3f_1003_ = lean_ctor_get(v_a_993_, 1);
v_cache_1004_ = lean_ctor_get_uint8(v_a_993_, sizeof(void*)*2);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_a_993_, 0);
lean_dec(v_unused_1015_);
v___x_1006_ = v_a_993_;
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_proof_x3f_1003_);
lean_dec(v_a_993_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1014_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_a_998_);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_proof_x3f_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*2, v_cache_1004_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1009_);
v___x_1011_ = v___x_1000_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_993_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1047_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_997_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_997_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_993_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1055_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_995_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_995_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_dec(v_a_991_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v___x_992_;
}
}
else
{
lean_dec(v_a_988_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v___x_990_;
}
}
else
{
lean_dec(v_a_986_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v___x_987_;
}
}
else
{
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v___x_985_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1063_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_983_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_983_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1071_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_981_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_981_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1079_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_979_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_979_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1087_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_977_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_977_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1095_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_975_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_975_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_a_969_);
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
v_a_1103_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_973_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_973_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = lean_grind_preprocess(v_e_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_1124_, v_msg_1125_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_1138_, v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec(v___y_1140_);
return v_res_1151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1159_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_1160_ = l_Lean_Name_append(v___x_1159_, v___x_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_1174_ = l_Lean_mkConst(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_1175_, lean_object* v_proof_1176_, lean_object* v_generation_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; 
lean_inc(v_a_1187_);
lean_inc_ref(v_a_1186_);
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
lean_inc_ref(v_a_1180_);
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_inc_ref(v_prop_1175_);
v___x_1189_ = lean_grind_preprocess(v_prop_1175_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v_expr_1191_; lean_object* v_proof_x3f_1192_; lean_object* v___y_1194_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v_expr_1191_ = lean_ctor_get(v_a_1190_, 0);
lean_inc_ref(v_expr_1191_);
v_proof_x3f_1192_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_proof_x3f_1192_);
lean_dec(v_a_1190_);
if (lean_obj_tag(v_proof_x3f_1192_) == 1)
{
lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_val_1211_ = lean_ctor_get(v_proof_x3f_1192_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_proof_x3f_1192_, 1);
v___x_1212_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_1191_);
lean_inc_ref(v_prop_1175_);
v___x_1213_ = l_Lean_mkApp4(v___x_1212_, v_prop_1175_, v_expr_1191_, v_val_1211_, v_proof_1176_);
v___y_1194_ = v___x_1213_;
goto v___jp_1193_;
}
else
{
lean_dec(v_proof_x3f_1192_);
v___y_1194_ = v_proof_1176_;
goto v___jp_1193_;
}
v___jp_1193_:
{
lean_object* v_toCold_1195_; lean_object* v_options_1196_; uint8_t v_hasTrace_1197_; 
v_toCold_1195_ = lean_ctor_get(v_a_1186_, 0);
v_options_1196_ = lean_ctor_get(v_toCold_1195_, 2);
v_hasTrace_1197_ = lean_ctor_get_uint8(v_options_1196_, sizeof(void*)*1);
if (v_hasTrace_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v_prop_1175_);
v___x_1198_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1191_, v___y_1194_, v_generation_1177_, v_a_1178_);
return v___x_1198_;
}
else
{
lean_object* v_inheritedTraceOptions_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_inheritedTraceOptions_1199_ = lean_ctor_get(v_toCold_1195_, 11);
v___x_1200_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1201_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1199_, v_options_1196_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v_prop_1175_);
v___x_1203_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1191_, v___y_1194_, v_generation_1177_, v_a_1178_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1204_ = l_Lean_MessageData_ofExpr(v_prop_1175_);
v___x_1205_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc_ref(v_expr_1191_);
v___x_1207_ = l_Lean_MessageData_ofExpr(v_expr_1191_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1200_, v___x_1208_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1209_, 1);
v___x_1210_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1191_, v___y_1194_, v_generation_1177_, v_a_1178_);
return v___x_1210_;
}
else
{
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_expr_1191_);
lean_dec(v_generation_1177_);
return v___x_1209_;
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_generation_1177_);
lean_dec_ref(v_proof_1176_);
lean_dec_ref(v_prop_1175_);
v_a_1214_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1189_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1189_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_1222_, lean_object* v_proof_1223_, lean_object* v_generation_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_1222_, v_proof_1223_, v_generation_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec(v_a_1225_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_1237_, lean_object* v_generation_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; 
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
lean_inc_ref(v_proof_1237_);
v___x_1250_ = lean_infer_type(v_proof_1237_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_toCold_1251_; lean_object* v_options_1252_; uint8_t v_hasTrace_1253_; 
v_toCold_1251_ = lean_ctor_get(v_a_1247_, 0);
v_options_1252_ = lean_ctor_get(v_toCold_1251_, 2);
v_hasTrace_1253_ = lean_ctor_get_uint8(v_options_1252_, sizeof(void*)*1);
if (v_hasTrace_1253_ == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1255_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1254_, v_proof_1237_, v_generation_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v_inheritedTraceOptions_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1250_, 1);
v_inheritedTraceOptions_1257_ = lean_ctor_get(v_toCold_1251_, 11);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1259_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1257_, v_options_1252_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1256_, v_proof_1237_, v_generation_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_inc(v_a_1256_);
v___x_1262_ = l_Lean_MessageData_ofExpr(v_a_1256_);
v___x_1263_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1258_, v___x_1262_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref_known(v___x_1263_, 1);
v___x_1264_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1256_, v_proof_1237_, v_generation_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1264_;
}
else
{
lean_dec(v_a_1256_);
lean_dec(v_generation_1238_);
lean_dec_ref(v_proof_1237_);
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_generation_1238_);
lean_dec_ref(v_proof_1237_);
v_a_1265_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1250_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1250_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_1273_, lean_object* v_generation_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_Grind_pushNewFact(v_proof_1273_, v_generation_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec(v_a_1275_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; 
v___x_1298_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_1287_, v_a_1294_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1299_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_1301_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1303_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = l_Lean_Meta_Grind_foldProjs(v_a_1305_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1307_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = l_Lean_Meta_Sym_canon(v_a_1309_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Meta_Sym_shareCommon(v_a_1311_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1312_;
}
else
{
return v___x_1310_;
}
}
else
{
return v___x_1308_;
}
}
else
{
return v___x_1306_;
}
}
else
{
return v___x_1304_;
}
}
else
{
return v___x_1302_;
}
}
else
{
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1325_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_preprocessLight(v_e_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec(v_a_1339_);
return v_res_1350_;
}
}
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Main(builtin);
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

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
lean_ctor_set(v___x_72_, 1, v___y_68_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2, v___x_71_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___y_69_);
lean_ctor_set(v___x_65_, 0, v_snd_63_);
v___x_74_ = v___x_65_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_snd_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___y_69_);
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
v___y_68_ = v_snd_82_;
v___y_69_ = v_snd_88_;
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
v___y_68_ = v_snd_82_;
v___y_69_ = v_snd_89_;
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
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(lean_object* v_e_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v_congrThms_226_; lean_object* v_simp_227_; lean_object* v_symSimp_228_; lean_object* v_symDSimp_229_; lean_object* v_lastTag_230_; lean_object* v_counters_231_; lean_object* v_splitDiags_232_; lean_object* v_ematchDiags_233_; lean_object* v_lawfulEqCmpMap_234_; lean_object* v_reflCmpMap_235_; lean_object* v_anchors_236_; lean_object* v_fvarAnchors_237_; lean_object* v_instanceMap_238_; lean_object* v_hoistedDecls_239_; lean_object* v_proofInfos_240_; lean_object* v_numBranches_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_299_; 
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
v_fvarAnchors_237_ = lean_ctor_get(v___x_225_, 11);
v_instanceMap_238_ = lean_ctor_get(v___x_225_, 12);
v_hoistedDecls_239_ = lean_ctor_get(v___x_225_, 13);
v_proofInfos_240_ = lean_ctor_get(v___x_225_, 14);
v_numBranches_241_ = lean_ctor_get(v___x_225_, 15);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_299_ == 0)
{
v___x_243_ = v___x_225_;
v_isShared_244_ = v_isSharedCheck_299_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_numBranches_241_);
lean_inc(v_proofInfos_240_);
lean_inc(v_hoistedDecls_239_);
lean_inc(v_instanceMap_238_);
lean_inc(v_fvarAnchors_237_);
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
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_299_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2);
v___x_246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 3, v___x_246_);
lean_ctor_set(v___x_243_, 2, v___x_245_);
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_congrThms_226_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_simp_227_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_lastTag_230_);
lean_ctor_set(v_reuseFailAlloc_298_, 5, v_counters_231_);
lean_ctor_set(v_reuseFailAlloc_298_, 6, v_splitDiags_232_);
lean_ctor_set(v_reuseFailAlloc_298_, 7, v_ematchDiags_233_);
lean_ctor_set(v_reuseFailAlloc_298_, 8, v_lawfulEqCmpMap_234_);
lean_ctor_set(v_reuseFailAlloc_298_, 9, v_reflCmpMap_235_);
lean_ctor_set(v_reuseFailAlloc_298_, 10, v_anchors_236_);
lean_ctor_set(v_reuseFailAlloc_298_, 11, v_fvarAnchors_237_);
lean_ctor_set(v_reuseFailAlloc_298_, 12, v_instanceMap_238_);
lean_ctor_set(v_reuseFailAlloc_298_, 13, v_hoistedDecls_239_);
lean_ctor_set(v_reuseFailAlloc_298_, 14, v_proofInfos_240_);
lean_ctor_set(v_reuseFailAlloc_298_, 15, v_numBranches_241_);
v___x_248_ = v_reuseFailAlloc_298_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v_symSimpMethods_250_; lean_object* v_symDSimpMethods_251_; lean_object* v___x_252_; 
v___x_249_ = lean_st_ref_put(v___y_217_, v___x_248_);
v_symSimpMethods_250_ = lean_ctor_get(v___y_216_, 2);
v_symDSimpMethods_251_ = lean_ctor_get(v___y_216_, 3);
lean_inc_ref(v_symDSimpMethods_251_);
lean_inc_ref(v_symSimpMethods_250_);
v___x_252_ = l_Lean_Meta_Grind_symNorm(v_e_214_, v_symSimpMethods_250_, v_symDSimpMethods_251_, v_symSimp_228_, v_symDSimp_229_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_289_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_289_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_289_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_289_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v_snd_257_; lean_object* v_fst_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; lean_object* v_congrThms_262_; lean_object* v_simp_263_; lean_object* v_lastTag_264_; lean_object* v_counters_265_; lean_object* v_splitDiags_266_; lean_object* v_ematchDiags_267_; lean_object* v_lawfulEqCmpMap_268_; lean_object* v_reflCmpMap_269_; lean_object* v_anchors_270_; lean_object* v_fvarAnchors_271_; lean_object* v_instanceMap_272_; lean_object* v_hoistedDecls_273_; lean_object* v_proofInfos_274_; lean_object* v_numBranches_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_286_; 
v_snd_257_ = lean_ctor_get(v_a_253_, 1);
lean_inc(v_snd_257_);
v_fst_258_ = lean_ctor_get(v_a_253_, 0);
lean_inc(v_fst_258_);
lean_dec(v_a_253_);
v_fst_259_ = lean_ctor_get(v_snd_257_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v_snd_257_, 1);
lean_inc(v_snd_260_);
lean_dec(v_snd_257_);
v___x_261_ = lean_st_ref_take(v___y_217_);
v_congrThms_262_ = lean_ctor_get(v___x_261_, 0);
v_simp_263_ = lean_ctor_get(v___x_261_, 1);
v_lastTag_264_ = lean_ctor_get(v___x_261_, 4);
v_counters_265_ = lean_ctor_get(v___x_261_, 5);
v_splitDiags_266_ = lean_ctor_get(v___x_261_, 6);
v_ematchDiags_267_ = lean_ctor_get(v___x_261_, 7);
v_lawfulEqCmpMap_268_ = lean_ctor_get(v___x_261_, 8);
v_reflCmpMap_269_ = lean_ctor_get(v___x_261_, 9);
v_anchors_270_ = lean_ctor_get(v___x_261_, 10);
v_fvarAnchors_271_ = lean_ctor_get(v___x_261_, 11);
v_instanceMap_272_ = lean_ctor_get(v___x_261_, 12);
v_hoistedDecls_273_ = lean_ctor_get(v___x_261_, 13);
v_proofInfos_274_ = lean_ctor_get(v___x_261_, 14);
v_numBranches_275_ = lean_ctor_get(v___x_261_, 15);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_287_ = lean_ctor_get(v___x_261_, 3);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v___x_261_, 2);
lean_dec(v_unused_288_);
v___x_277_ = v___x_261_;
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_numBranches_275_);
lean_inc(v_proofInfos_274_);
lean_inc(v_hoistedDecls_273_);
lean_inc(v_instanceMap_272_);
lean_inc(v_fvarAnchors_271_);
lean_inc(v_anchors_270_);
lean_inc(v_reflCmpMap_269_);
lean_inc(v_lawfulEqCmpMap_268_);
lean_inc(v_ematchDiags_267_);
lean_inc(v_splitDiags_266_);
lean_inc(v_counters_265_);
lean_inc(v_lastTag_264_);
lean_inc(v_simp_263_);
lean_inc(v_congrThms_262_);
lean_dec(v___x_261_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 3, v_snd_260_);
lean_ctor_set(v___x_277_, 2, v_fst_259_);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_congrThms_262_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_simp_263_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_fst_259_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_snd_260_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_lastTag_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v_counters_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_splitDiags_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 7, v_ematchDiags_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 8, v_lawfulEqCmpMap_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 9, v_reflCmpMap_269_);
lean_ctor_set(v_reuseFailAlloc_285_, 10, v_anchors_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 11, v_fvarAnchors_271_);
lean_ctor_set(v_reuseFailAlloc_285_, 12, v_instanceMap_272_);
lean_ctor_set(v_reuseFailAlloc_285_, 13, v_hoistedDecls_273_);
lean_ctor_set(v_reuseFailAlloc_285_, 14, v_proofInfos_274_);
lean_ctor_set(v_reuseFailAlloc_285_, 15, v_numBranches_275_);
v___x_280_ = v_reuseFailAlloc_285_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_st_ref_put(v___y_217_, v___x_280_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v_fst_258_);
v___x_283_ = v___x_255_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_fst_258_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_252_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_252_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed(lean_object* v_e_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(v_e_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(lean_object* v_e_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___f_324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_324_, 0, v_e_313_);
v___x_325_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_321_);
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_327_ = lean_box(0);
v___x_328_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_326_, v___x_325_, v___f_324_, v___x_327_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec_ref(v___x_325_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___boxed(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(lean_object* v_e_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_foldProjs(v_e_346_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = l_Lean_Meta_Sym_preprocessExpr(v_a_358_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v_congrThms_362_; lean_object* v_simp_363_; lean_object* v_symSimp_364_; lean_object* v_symDSimp_365_; lean_object* v_lastTag_366_; lean_object* v_counters_367_; lean_object* v_splitDiags_368_; lean_object* v_ematchDiags_369_; lean_object* v_lawfulEqCmpMap_370_; lean_object* v_reflCmpMap_371_; lean_object* v_anchors_372_; lean_object* v_fvarAnchors_373_; lean_object* v_instanceMap_374_; lean_object* v_hoistedDecls_375_; lean_object* v_proofInfos_376_; lean_object* v_numBranches_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_437_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_st_ref_take(v___y_349_);
v_congrThms_362_ = lean_ctor_get(v___x_361_, 0);
v_simp_363_ = lean_ctor_get(v___x_361_, 1);
v_symSimp_364_ = lean_ctor_get(v___x_361_, 2);
v_symDSimp_365_ = lean_ctor_get(v___x_361_, 3);
v_lastTag_366_ = lean_ctor_get(v___x_361_, 4);
v_counters_367_ = lean_ctor_get(v___x_361_, 5);
v_splitDiags_368_ = lean_ctor_get(v___x_361_, 6);
v_ematchDiags_369_ = lean_ctor_get(v___x_361_, 7);
v_lawfulEqCmpMap_370_ = lean_ctor_get(v___x_361_, 8);
v_reflCmpMap_371_ = lean_ctor_get(v___x_361_, 9);
v_anchors_372_ = lean_ctor_get(v___x_361_, 10);
v_fvarAnchors_373_ = lean_ctor_get(v___x_361_, 11);
v_instanceMap_374_ = lean_ctor_get(v___x_361_, 12);
v_hoistedDecls_375_ = lean_ctor_get(v___x_361_, 13);
v_proofInfos_376_ = lean_ctor_get(v___x_361_, 14);
v_numBranches_377_ = lean_ctor_get(v___x_361_, 15);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_437_ == 0)
{
v___x_379_ = v___x_361_;
v_isShared_380_ = v_isSharedCheck_437_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_numBranches_377_);
lean_inc(v_proofInfos_376_);
lean_inc(v_hoistedDecls_375_);
lean_inc(v_instanceMap_374_);
lean_inc(v_fvarAnchors_373_);
lean_inc(v_anchors_372_);
lean_inc(v_reflCmpMap_371_);
lean_inc(v_lawfulEqCmpMap_370_);
lean_inc(v_ematchDiags_369_);
lean_inc(v_splitDiags_368_);
lean_inc(v_counters_367_);
lean_inc(v_lastTag_366_);
lean_inc(v_symDSimp_365_);
lean_inc(v_symSimp_364_);
lean_inc(v_simp_363_);
lean_inc(v_congrThms_362_);
lean_dec(v___x_361_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_437_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 3, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_congrThms_362_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_simp_363_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_symSimp_364_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_lastTag_366_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_counters_367_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_splitDiags_368_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_ematchDiags_369_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_lawfulEqCmpMap_370_);
lean_ctor_set(v_reuseFailAlloc_436_, 9, v_reflCmpMap_371_);
lean_ctor_set(v_reuseFailAlloc_436_, 10, v_anchors_372_);
lean_ctor_set(v_reuseFailAlloc_436_, 11, v_fvarAnchors_373_);
lean_ctor_set(v_reuseFailAlloc_436_, 12, v_instanceMap_374_);
lean_ctor_set(v_reuseFailAlloc_436_, 13, v_hoistedDecls_375_);
lean_ctor_set(v_reuseFailAlloc_436_, 14, v_proofInfos_376_);
lean_ctor_set(v_reuseFailAlloc_436_, 15, v_numBranches_377_);
v___x_383_ = v_reuseFailAlloc_436_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v_symDSimpMethods_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_384_ = lean_st_ref_put(v___y_349_, v___x_383_);
v_symDSimpMethods_385_ = lean_ctor_get(v___y_348_, 3);
lean_inc(v_a_360_);
v___x_386_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_386_, 0, v_a_360_);
v___x_387_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
lean_inc_ref(v_symDSimpMethods_385_);
v___x_388_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_386_, v_symDSimpMethods_385_, v___x_387_, v_symDSimp_365_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_427_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_427_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v___x_395_; lean_object* v_congrThms_396_; lean_object* v_simp_397_; lean_object* v_symSimp_398_; lean_object* v_lastTag_399_; lean_object* v_counters_400_; lean_object* v_splitDiags_401_; lean_object* v_ematchDiags_402_; lean_object* v_lawfulEqCmpMap_403_; lean_object* v_reflCmpMap_404_; lean_object* v_anchors_405_; lean_object* v_fvarAnchors_406_; lean_object* v_instanceMap_407_; lean_object* v_hoistedDecls_408_; lean_object* v_proofInfos_409_; lean_object* v_numBranches_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_425_; 
v_fst_393_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v_a_389_, 1);
lean_inc(v_snd_394_);
lean_dec(v_a_389_);
v___x_395_ = lean_st_ref_take(v___y_349_);
v_congrThms_396_ = lean_ctor_get(v___x_395_, 0);
v_simp_397_ = lean_ctor_get(v___x_395_, 1);
v_symSimp_398_ = lean_ctor_get(v___x_395_, 2);
v_lastTag_399_ = lean_ctor_get(v___x_395_, 4);
v_counters_400_ = lean_ctor_get(v___x_395_, 5);
v_splitDiags_401_ = lean_ctor_get(v___x_395_, 6);
v_ematchDiags_402_ = lean_ctor_get(v___x_395_, 7);
v_lawfulEqCmpMap_403_ = lean_ctor_get(v___x_395_, 8);
v_reflCmpMap_404_ = lean_ctor_get(v___x_395_, 9);
v_anchors_405_ = lean_ctor_get(v___x_395_, 10);
v_fvarAnchors_406_ = lean_ctor_get(v___x_395_, 11);
v_instanceMap_407_ = lean_ctor_get(v___x_395_, 12);
v_hoistedDecls_408_ = lean_ctor_get(v___x_395_, 13);
v_proofInfos_409_ = lean_ctor_get(v___x_395_, 14);
v_numBranches_410_ = lean_ctor_get(v___x_395_, 15);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_395_, 3);
lean_dec(v_unused_426_);
v___x_412_ = v___x_395_;
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_numBranches_410_);
lean_inc(v_proofInfos_409_);
lean_inc(v_hoistedDecls_408_);
lean_inc(v_instanceMap_407_);
lean_inc(v_fvarAnchors_406_);
lean_inc(v_anchors_405_);
lean_inc(v_reflCmpMap_404_);
lean_inc(v_lawfulEqCmpMap_403_);
lean_inc(v_ematchDiags_402_);
lean_inc(v_splitDiags_401_);
lean_inc(v_counters_400_);
lean_inc(v_lastTag_399_);
lean_inc(v_symSimp_398_);
lean_inc(v_simp_397_);
lean_inc(v_congrThms_396_);
lean_dec(v___x_395_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 3, v_snd_394_);
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_congrThms_396_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_simp_397_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_symSimp_398_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_snd_394_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_lastTag_399_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_counters_400_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_splitDiags_401_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_ematchDiags_402_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_lawfulEqCmpMap_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 9, v_reflCmpMap_404_);
lean_ctor_set(v_reuseFailAlloc_424_, 10, v_anchors_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 11, v_fvarAnchors_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 12, v_instanceMap_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 13, v_hoistedDecls_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 14, v_proofInfos_409_);
lean_ctor_set(v_reuseFailAlloc_424_, 15, v_numBranches_410_);
v___x_415_ = v_reuseFailAlloc_424_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_st_ref_put(v___y_349_, v___x_415_);
if (lean_obj_tag(v_fst_393_) == 0)
{
lean_object* v___x_418_; 
lean_dec_ref_known(v_fst_393_, 0);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_a_360_);
v___x_418_ = v___x_391_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_360_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v_e_x27_420_; lean_object* v___x_422_; 
lean_dec(v_a_360_);
v_e_x27_420_ = lean_ctor_get(v_fst_393_, 0);
lean_inc_ref(v_e_x27_420_);
lean_dec_ref_known(v_fst_393_, 1);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_e_x27_420_);
v___x_422_ = v___x_391_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_e_x27_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_a_360_);
v_a_428_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_388_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_388_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
else
{
return v___x_359_;
}
}
else
{
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(v_e_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___f_462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_462_, 0, v_e_451_);
v___x_463_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_459_);
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_464_, v___x_463_, v___f_462_, v___x_465_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec_ref(v___x_463_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___boxed(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
return v_res_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
v___x_480_ = lean_unsigned_to_nat(16u);
v___x_481_ = lean_mk_array(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_489_ = 1;
v___x_490_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_487_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*2, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_unsigned_to_nat(32u);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6(void){
_start:
{
size_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_497_ = ((size_t)5ULL);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_unsigned_to_nat(32u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
v___x_501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5);
v___x_502_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
lean_ctor_set(v___x_502_, 2, v___x_498_);
lean_ctor_set(v___x_502_, 3, v___x_498_);
lean_ctor_set_usize(v___x_502_, 4, v___x_497_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6);
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_ctor_set(v___x_505_, 2, v___x_504_);
lean_ctor_set(v___x_505_, 3, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8(void){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_506_ = lean_box(0);
v___x_507_ = 0;
v___x_508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4);
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3);
v___x_513_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
lean_ctor_set(v___x_513_, 3, v___x_510_);
lean_ctor_set(v___x_513_, 4, v___x_509_);
lean_ctor_set(v___x_513_, 5, v___x_508_);
lean_ctor_set(v___x_513_, 6, v___x_506_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7, v___x_507_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7 + 1, v___x_507_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(lean_object* v_e_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_congrThms_526_; lean_object* v_simp_527_; lean_object* v_symSimp_528_; lean_object* v_symDSimp_529_; lean_object* v_lastTag_530_; lean_object* v_counters_531_; lean_object* v_splitDiags_532_; lean_object* v_ematchDiags_533_; lean_object* v_lawfulEqCmpMap_534_; lean_object* v_reflCmpMap_535_; lean_object* v_anchors_536_; lean_object* v_fvarAnchors_537_; lean_object* v_instanceMap_538_; lean_object* v_hoistedDecls_539_; lean_object* v_proofInfos_540_; lean_object* v_numBranches_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_596_; 
v___x_525_ = lean_st_ref_take(v___y_517_);
v_congrThms_526_ = lean_ctor_get(v___x_525_, 0);
v_simp_527_ = lean_ctor_get(v___x_525_, 1);
v_symSimp_528_ = lean_ctor_get(v___x_525_, 2);
v_symDSimp_529_ = lean_ctor_get(v___x_525_, 3);
v_lastTag_530_ = lean_ctor_get(v___x_525_, 4);
v_counters_531_ = lean_ctor_get(v___x_525_, 5);
v_splitDiags_532_ = lean_ctor_get(v___x_525_, 6);
v_ematchDiags_533_ = lean_ctor_get(v___x_525_, 7);
v_lawfulEqCmpMap_534_ = lean_ctor_get(v___x_525_, 8);
v_reflCmpMap_535_ = lean_ctor_get(v___x_525_, 9);
v_anchors_536_ = lean_ctor_get(v___x_525_, 10);
v_fvarAnchors_537_ = lean_ctor_get(v___x_525_, 11);
v_instanceMap_538_ = lean_ctor_get(v___x_525_, 12);
v_hoistedDecls_539_ = lean_ctor_get(v___x_525_, 13);
v_proofInfos_540_ = lean_ctor_get(v___x_525_, 14);
v_numBranches_541_ = lean_ctor_get(v___x_525_, 15);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_596_ == 0)
{
v___x_543_ = v___x_525_;
v_isShared_544_ = v_isSharedCheck_596_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_numBranches_541_);
lean_inc(v_proofInfos_540_);
lean_inc(v_hoistedDecls_539_);
lean_inc(v_instanceMap_538_);
lean_inc(v_fvarAnchors_537_);
lean_inc(v_anchors_536_);
lean_inc(v_reflCmpMap_535_);
lean_inc(v_lawfulEqCmpMap_534_);
lean_inc(v_ematchDiags_533_);
lean_inc(v_splitDiags_532_);
lean_inc(v_counters_531_);
lean_inc(v_lastTag_530_);
lean_inc(v_symDSimp_529_);
lean_inc(v_symSimp_528_);
lean_inc(v_simp_527_);
lean_inc(v_congrThms_526_);
lean_dec(v___x_525_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_596_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_congrThms_526_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_symSimp_528_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_symDSimp_529_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_lastTag_530_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_counters_531_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_splitDiags_532_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_ematchDiags_533_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_lawfulEqCmpMap_534_);
lean_ctor_set(v_reuseFailAlloc_595_, 9, v_reflCmpMap_535_);
lean_ctor_set(v_reuseFailAlloc_595_, 10, v_anchors_536_);
lean_ctor_set(v_reuseFailAlloc_595_, 11, v_fvarAnchors_537_);
lean_ctor_set(v_reuseFailAlloc_595_, 12, v_instanceMap_538_);
lean_ctor_set(v_reuseFailAlloc_595_, 13, v_hoistedDecls_539_);
lean_ctor_set(v_reuseFailAlloc_595_, 14, v_proofInfos_540_);
lean_ctor_set(v_reuseFailAlloc_595_, 15, v_numBranches_541_);
v___x_547_ = v_reuseFailAlloc_595_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v_simp_549_; lean_object* v_simpMethods_550_; lean_object* v___x_551_; 
v___x_548_ = lean_st_ref_put(v___y_517_, v___x_547_);
v_simp_549_ = lean_ctor_get(v___y_516_, 0);
v_simpMethods_550_ = lean_ctor_get(v___y_516_, 1);
lean_inc_ref(v_simpMethods_550_);
lean_inc_ref(v_simp_549_);
v___x_551_ = l_Lean_Meta_Simp_mainCore(v_e_514_, v_simp_549_, v_simp_527_, v_simpMethods_550_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_586_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_586_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_586_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_586_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; lean_object* v_congrThms_559_; lean_object* v_symSimp_560_; lean_object* v_symDSimp_561_; lean_object* v_lastTag_562_; lean_object* v_counters_563_; lean_object* v_splitDiags_564_; lean_object* v_ematchDiags_565_; lean_object* v_lawfulEqCmpMap_566_; lean_object* v_reflCmpMap_567_; lean_object* v_anchors_568_; lean_object* v_fvarAnchors_569_; lean_object* v_instanceMap_570_; lean_object* v_hoistedDecls_571_; lean_object* v_proofInfos_572_; lean_object* v_numBranches_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_fst_556_ = lean_ctor_get(v_a_552_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v_a_552_, 1);
lean_inc(v_snd_557_);
lean_dec(v_a_552_);
v___x_558_ = lean_st_ref_take(v___y_517_);
v_congrThms_559_ = lean_ctor_get(v___x_558_, 0);
v_symSimp_560_ = lean_ctor_get(v___x_558_, 2);
v_symDSimp_561_ = lean_ctor_get(v___x_558_, 3);
v_lastTag_562_ = lean_ctor_get(v___x_558_, 4);
v_counters_563_ = lean_ctor_get(v___x_558_, 5);
v_splitDiags_564_ = lean_ctor_get(v___x_558_, 6);
v_ematchDiags_565_ = lean_ctor_get(v___x_558_, 7);
v_lawfulEqCmpMap_566_ = lean_ctor_get(v___x_558_, 8);
v_reflCmpMap_567_ = lean_ctor_get(v___x_558_, 9);
v_anchors_568_ = lean_ctor_get(v___x_558_, 10);
v_fvarAnchors_569_ = lean_ctor_get(v___x_558_, 11);
v_instanceMap_570_ = lean_ctor_get(v___x_558_, 12);
v_hoistedDecls_571_ = lean_ctor_get(v___x_558_, 13);
v_proofInfos_572_ = lean_ctor_get(v___x_558_, 14);
v_numBranches_573_ = lean_ctor_get(v___x_558_, 15);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_558_, 1);
lean_dec(v_unused_585_);
v___x_575_ = v___x_558_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_numBranches_573_);
lean_inc(v_proofInfos_572_);
lean_inc(v_hoistedDecls_571_);
lean_inc(v_instanceMap_570_);
lean_inc(v_fvarAnchors_569_);
lean_inc(v_anchors_568_);
lean_inc(v_reflCmpMap_567_);
lean_inc(v_lawfulEqCmpMap_566_);
lean_inc(v_ematchDiags_565_);
lean_inc(v_splitDiags_564_);
lean_inc(v_counters_563_);
lean_inc(v_lastTag_562_);
lean_inc(v_symDSimp_561_);
lean_inc(v_symSimp_560_);
lean_inc(v_congrThms_559_);
lean_dec(v___x_558_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 1, v_snd_557_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_congrThms_559_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_snd_557_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_symSimp_560_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_symDSimp_561_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_lastTag_562_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v_counters_563_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_splitDiags_564_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_ematchDiags_565_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_lawfulEqCmpMap_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 9, v_reflCmpMap_567_);
lean_ctor_set(v_reuseFailAlloc_583_, 10, v_anchors_568_);
lean_ctor_set(v_reuseFailAlloc_583_, 11, v_fvarAnchors_569_);
lean_ctor_set(v_reuseFailAlloc_583_, 12, v_instanceMap_570_);
lean_ctor_set(v_reuseFailAlloc_583_, 13, v_hoistedDecls_571_);
lean_ctor_set(v_reuseFailAlloc_583_, 14, v_proofInfos_572_);
lean_ctor_set(v_reuseFailAlloc_583_, 15, v_numBranches_573_);
v___x_578_ = v_reuseFailAlloc_583_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_st_ref_put(v___y_517_, v___x_578_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v_fst_556_);
v___x_581_ = v___x_554_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_fst_556_);
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
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_587_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_551_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_551_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed(lean_object* v_e_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(v_e_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(lean_object* v_e_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___f_620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_620_, 0, v_e_609_);
v___x_621_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_617_);
v___x_622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_623_ = lean_box(0);
v___x_624_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_622_, v___x_621_, v___f_620_, v___x_623_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec_ref(v___x_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___boxed(lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(lean_object* v_e_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_congrThms_649_; lean_object* v_simp_650_; lean_object* v_symSimp_651_; lean_object* v_symDSimp_652_; lean_object* v_lastTag_653_; lean_object* v_counters_654_; lean_object* v_splitDiags_655_; lean_object* v_ematchDiags_656_; lean_object* v_lawfulEqCmpMap_657_; lean_object* v_reflCmpMap_658_; lean_object* v_anchors_659_; lean_object* v_fvarAnchors_660_; lean_object* v_instanceMap_661_; lean_object* v_hoistedDecls_662_; lean_object* v_proofInfos_663_; lean_object* v_numBranches_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_721_; 
v___x_648_ = lean_st_ref_take(v___y_640_);
v_congrThms_649_ = lean_ctor_get(v___x_648_, 0);
v_simp_650_ = lean_ctor_get(v___x_648_, 1);
v_symSimp_651_ = lean_ctor_get(v___x_648_, 2);
v_symDSimp_652_ = lean_ctor_get(v___x_648_, 3);
v_lastTag_653_ = lean_ctor_get(v___x_648_, 4);
v_counters_654_ = lean_ctor_get(v___x_648_, 5);
v_splitDiags_655_ = lean_ctor_get(v___x_648_, 6);
v_ematchDiags_656_ = lean_ctor_get(v___x_648_, 7);
v_lawfulEqCmpMap_657_ = lean_ctor_get(v___x_648_, 8);
v_reflCmpMap_658_ = lean_ctor_get(v___x_648_, 9);
v_anchors_659_ = lean_ctor_get(v___x_648_, 10);
v_fvarAnchors_660_ = lean_ctor_get(v___x_648_, 11);
v_instanceMap_661_ = lean_ctor_get(v___x_648_, 12);
v_hoistedDecls_662_ = lean_ctor_get(v___x_648_, 13);
v_proofInfos_663_ = lean_ctor_get(v___x_648_, 14);
v_numBranches_664_ = lean_ctor_get(v___x_648_, 15);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_721_ == 0)
{
v___x_666_ = v___x_648_;
v_isShared_667_ = v_isSharedCheck_721_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_numBranches_664_);
lean_inc(v_proofInfos_663_);
lean_inc(v_hoistedDecls_662_);
lean_inc(v_instanceMap_661_);
lean_inc(v_fvarAnchors_660_);
lean_inc(v_anchors_659_);
lean_inc(v_reflCmpMap_658_);
lean_inc(v_lawfulEqCmpMap_657_);
lean_inc(v_ematchDiags_656_);
lean_inc(v_splitDiags_655_);
lean_inc(v_counters_654_);
lean_inc(v_lastTag_653_);
lean_inc(v_symDSimp_652_);
lean_inc(v_symSimp_651_);
lean_inc(v_simp_650_);
lean_inc(v_congrThms_649_);
lean_dec(v___x_648_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_721_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_668_ = lean_unsigned_to_nat(32u);
v___x_669_ = lean_mk_empty_array_with_capacity(v___x_668_);
lean_dec_ref(v___x_669_);
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_congrThms_649_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_symSimp_651_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_symDSimp_652_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_lastTag_653_);
lean_ctor_set(v_reuseFailAlloc_720_, 5, v_counters_654_);
lean_ctor_set(v_reuseFailAlloc_720_, 6, v_splitDiags_655_);
lean_ctor_set(v_reuseFailAlloc_720_, 7, v_ematchDiags_656_);
lean_ctor_set(v_reuseFailAlloc_720_, 8, v_lawfulEqCmpMap_657_);
lean_ctor_set(v_reuseFailAlloc_720_, 9, v_reflCmpMap_658_);
lean_ctor_set(v_reuseFailAlloc_720_, 10, v_anchors_659_);
lean_ctor_set(v_reuseFailAlloc_720_, 11, v_fvarAnchors_660_);
lean_ctor_set(v_reuseFailAlloc_720_, 12, v_instanceMap_661_);
lean_ctor_set(v_reuseFailAlloc_720_, 13, v_hoistedDecls_662_);
lean_ctor_set(v_reuseFailAlloc_720_, 14, v_proofInfos_663_);
lean_ctor_set(v_reuseFailAlloc_720_, 15, v_numBranches_664_);
v___x_672_ = v_reuseFailAlloc_720_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v_simp_674_; lean_object* v_simpMethods_675_; lean_object* v___x_676_; 
v___x_673_ = lean_st_ref_put(v___y_640_, v___x_672_);
v_simp_674_ = lean_ctor_get(v___y_639_, 0);
v_simpMethods_675_ = lean_ctor_get(v___y_639_, 1);
lean_inc_ref(v_simpMethods_675_);
lean_inc_ref(v_simp_674_);
v___x_676_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_637_, v_simp_674_, v_simp_650_, v_simpMethods_675_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_711_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_711_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_711_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_711_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_683_; lean_object* v_congrThms_684_; lean_object* v_symSimp_685_; lean_object* v_symDSimp_686_; lean_object* v_lastTag_687_; lean_object* v_counters_688_; lean_object* v_splitDiags_689_; lean_object* v_ematchDiags_690_; lean_object* v_lawfulEqCmpMap_691_; lean_object* v_reflCmpMap_692_; lean_object* v_anchors_693_; lean_object* v_fvarAnchors_694_; lean_object* v_instanceMap_695_; lean_object* v_hoistedDecls_696_; lean_object* v_proofInfos_697_; lean_object* v_numBranches_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_709_; 
v_fst_681_ = lean_ctor_get(v_a_677_, 0);
lean_inc(v_fst_681_);
v_snd_682_ = lean_ctor_get(v_a_677_, 1);
lean_inc(v_snd_682_);
lean_dec(v_a_677_);
v___x_683_ = lean_st_ref_take(v___y_640_);
v_congrThms_684_ = lean_ctor_get(v___x_683_, 0);
v_symSimp_685_ = lean_ctor_get(v___x_683_, 2);
v_symDSimp_686_ = lean_ctor_get(v___x_683_, 3);
v_lastTag_687_ = lean_ctor_get(v___x_683_, 4);
v_counters_688_ = lean_ctor_get(v___x_683_, 5);
v_splitDiags_689_ = lean_ctor_get(v___x_683_, 6);
v_ematchDiags_690_ = lean_ctor_get(v___x_683_, 7);
v_lawfulEqCmpMap_691_ = lean_ctor_get(v___x_683_, 8);
v_reflCmpMap_692_ = lean_ctor_get(v___x_683_, 9);
v_anchors_693_ = lean_ctor_get(v___x_683_, 10);
v_fvarAnchors_694_ = lean_ctor_get(v___x_683_, 11);
v_instanceMap_695_ = lean_ctor_get(v___x_683_, 12);
v_hoistedDecls_696_ = lean_ctor_get(v___x_683_, 13);
v_proofInfos_697_ = lean_ctor_get(v___x_683_, 14);
v_numBranches_698_ = lean_ctor_get(v___x_683_, 15);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_683_, 1);
lean_dec(v_unused_710_);
v___x_700_ = v___x_683_;
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_numBranches_698_);
lean_inc(v_proofInfos_697_);
lean_inc(v_hoistedDecls_696_);
lean_inc(v_instanceMap_695_);
lean_inc(v_fvarAnchors_694_);
lean_inc(v_anchors_693_);
lean_inc(v_reflCmpMap_692_);
lean_inc(v_lawfulEqCmpMap_691_);
lean_inc(v_ematchDiags_690_);
lean_inc(v_splitDiags_689_);
lean_inc(v_counters_688_);
lean_inc(v_lastTag_687_);
lean_inc(v_symDSimp_686_);
lean_inc(v_symSimp_685_);
lean_inc(v_congrThms_684_);
lean_dec(v___x_683_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_snd_682_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_congrThms_684_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_snd_682_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_symSimp_685_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_symDSimp_686_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_lastTag_687_);
lean_ctor_set(v_reuseFailAlloc_708_, 5, v_counters_688_);
lean_ctor_set(v_reuseFailAlloc_708_, 6, v_splitDiags_689_);
lean_ctor_set(v_reuseFailAlloc_708_, 7, v_ematchDiags_690_);
lean_ctor_set(v_reuseFailAlloc_708_, 8, v_lawfulEqCmpMap_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 9, v_reflCmpMap_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 10, v_anchors_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 11, v_fvarAnchors_694_);
lean_ctor_set(v_reuseFailAlloc_708_, 12, v_instanceMap_695_);
lean_ctor_set(v_reuseFailAlloc_708_, 13, v_hoistedDecls_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 14, v_proofInfos_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 15, v_numBranches_698_);
v___x_703_ = v_reuseFailAlloc_708_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_st_ref_put(v___y_640_, v___x_703_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_fst_681_);
v___x_706_ = v___x_679_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_681_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_712_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_676_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_676_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed(lean_object* v_e_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(v_e_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___f_745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_745_, 0, v_e_734_);
v___x_746_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_742_);
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_747_, v___x_746_, v___f_745_, v___x_748_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec_ref(v___x_746_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___boxed(lean_object* v_e_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_a_774_; uint8_t v___x_775_; 
v___x_773_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_770_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_773_);
v___x_775_ = lean_unbox(v_a_774_);
lean_dec(v_a_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_Grind_simpCore(v_e_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_a_802_; uint8_t v___x_803_; 
v___x_801_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_798_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_unbox(v_a_802_);
lean_dec(v_a_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Meta_Grind_dsimpCore(v_e_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = l_Lean_Expr_hasMVar(v_e_818_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_e_818_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v_mctx_824_; lean_object* v___x_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v___x_828_; lean_object* v_cache_829_; lean_object* v_zetaDeltaFVarIds_830_; lean_object* v_postponed_831_; lean_object* v_diag_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_841_; 
v___x_823_ = lean_st_ref_get(v___y_819_);
v_mctx_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_ref(v_mctx_824_);
lean_dec(v___x_823_);
v___x_825_ = l_Lean_instantiateMVarsCore(v_mctx_824_, v_e_818_);
v_fst_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_fst_826_);
v_snd_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc(v_snd_827_);
lean_dec_ref(v___x_825_);
v___x_828_ = lean_st_ref_take(v___y_819_);
v_cache_829_ = lean_ctor_get(v___x_828_, 1);
v_zetaDeltaFVarIds_830_ = lean_ctor_get(v___x_828_, 2);
v_postponed_831_ = lean_ctor_get(v___x_828_, 3);
v_diag_832_ = lean_ctor_get(v___x_828_, 4);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_842_);
v___x_834_ = v___x_828_;
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_diag_832_);
lean_inc(v_postponed_831_);
lean_inc(v_zetaDeltaFVarIds_830_);
lean_inc(v_cache_829_);
lean_dec(v___x_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v_snd_827_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_snd_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_cache_829_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_zetaDeltaFVarIds_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_postponed_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_diag_832_);
v___x_837_ = v_reuseFailAlloc_840_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_st_ref_put(v___y_819_, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_fst_826_);
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_843_, v___y_844_);
lean_dec(v___y_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_847_, v___y_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
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
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_env_880_; uint8_t v___x_881_; lean_object* v_env_882_; lean_object* v___x_883_; lean_object* v_toCold_884_; lean_object* v_mctx_885_; lean_object* v_lctx_886_; lean_object* v_options_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_879_ = lean_st_ref_get(v___y_877_);
v_env_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_env_880_);
lean_dec(v___x_879_);
v___x_881_ = 0;
v_env_882_ = l_Lean_Environment_setRecordingDeps(v_env_880_, v___x_881_);
v___x_883_ = lean_st_ref_get(v___y_875_);
v_toCold_884_ = lean_ctor_get(v___y_876_, 0);
v_mctx_885_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_mctx_885_);
lean_dec(v___x_883_);
v_lctx_886_ = lean_ctor_get(v___y_874_, 2);
v_options_887_ = lean_ctor_get(v_toCold_884_, 2);
lean_inc_ref(v_options_887_);
lean_inc_ref(v_lctx_886_);
v___x_888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_888_, 0, v_env_882_);
lean_ctor_set(v___x_888_, 1, v_mctx_885_);
lean_ctor_set(v___x_888_, 2, v_lctx_886_);
lean_ctor_set(v___x_888_, 3, v_options_887_);
v___x_889_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_msgData_873_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_898_; double v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_float_of_nat(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_903_, lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_ref_910_; lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_957_; 
v_ref_910_ = lean_ctor_get(v___y_907_, 2);
v___x_911_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_957_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_957_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_957_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v_traceState_917_; lean_object* v_env_918_; lean_object* v_nextMacroScope_919_; lean_object* v_ngen_920_; lean_object* v_auxDeclNGen_921_; lean_object* v_cache_922_; lean_object* v_recordedDeps_923_; lean_object* v_messages_924_; lean_object* v_infoState_925_; lean_object* v_snapshotTasks_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_956_; 
v___x_916_ = lean_st_ref_take(v___y_908_);
v_traceState_917_ = lean_ctor_get(v___x_916_, 4);
v_env_918_ = lean_ctor_get(v___x_916_, 0);
v_nextMacroScope_919_ = lean_ctor_get(v___x_916_, 1);
v_ngen_920_ = lean_ctor_get(v___x_916_, 2);
v_auxDeclNGen_921_ = lean_ctor_get(v___x_916_, 3);
v_cache_922_ = lean_ctor_get(v___x_916_, 5);
v_recordedDeps_923_ = lean_ctor_get(v___x_916_, 6);
v_messages_924_ = lean_ctor_get(v___x_916_, 7);
v_infoState_925_ = lean_ctor_get(v___x_916_, 8);
v_snapshotTasks_926_ = lean_ctor_get(v___x_916_, 9);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_956_ == 0)
{
v___x_928_ = v___x_916_;
v_isShared_929_ = v_isSharedCheck_956_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snapshotTasks_926_);
lean_inc(v_infoState_925_);
lean_inc(v_messages_924_);
lean_inc(v_recordedDeps_923_);
lean_inc(v_cache_922_);
lean_inc(v_traceState_917_);
lean_inc(v_auxDeclNGen_921_);
lean_inc(v_ngen_920_);
lean_inc(v_nextMacroScope_919_);
lean_inc(v_env_918_);
lean_dec(v___x_916_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_956_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint64_t v_tid_930_; lean_object* v_traces_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_955_; 
v_tid_930_ = lean_ctor_get_uint64(v_traceState_917_, sizeof(void*)*1);
v_traces_931_ = lean_ctor_get(v_traceState_917_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_traceState_917_);
if (v_isSharedCheck_955_ == 0)
{
v___x_933_ = v_traceState_917_;
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_traces_931_);
lean_dec(v_traceState_917_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; double v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_935_ = lean_box(0);
v___x_936_ = lean_box(0);
v___x_937_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_938_ = 0;
v___x_939_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_940_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_940_, 0, v_cls_903_);
lean_ctor_set(v___x_940_, 1, v___x_936_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3, v___x_937_);
lean_ctor_set_float(v___x_940_, sizeof(void*)*3 + 8, v___x_937_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 16, v___x_938_);
v___x_941_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_942_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v_a_912_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_inc(v_ref_910_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_ref_910_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_PersistentArray_push___redArg(v_traces_931_, v___x_943_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_944_);
v___x_946_ = v___x_933_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_944_);
lean_ctor_set_uint64(v_reuseFailAlloc_954_, sizeof(void*)*1, v_tid_930_);
v___x_946_ = v_reuseFailAlloc_954_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 4, v___x_946_);
v___x_948_ = v___x_928_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_env_918_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_nextMacroScope_919_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_ngen_920_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_auxDeclNGen_921_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v_recordedDeps_923_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_messages_924_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v_infoState_925_);
lean_ctor_set(v_reuseFailAlloc_953_, 9, v_snapshotTasks_926_);
v___x_948_ = v_reuseFailAlloc_953_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_st_ref_put(v___y_908_, v___x_948_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_935_);
v___x_951_ = v___x_914_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_935_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_958_, v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_975_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_976_ = l_Lean_Name_append(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_994_; 
v___x_992_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_980_, v_a_988_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc_n(v_a_993_, 2);
lean_dec_ref(v___x_992_);
v___x_994_ = l_Lean_Meta_Grind_simpCore(v_a_993_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v_expr_996_; lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v_expr_996_ = lean_ctor_get(v_a_995_, 0);
lean_inc_ref(v_expr_996_);
v___x_997_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_996_, v_a_988_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_Meta_Sym_unfoldReducible(v_a_998_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_1000_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_1002_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1004_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_Meta_Grind_foldProjs(v_a_1006_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1008_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_1010_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_n(v_a_1012_, 2);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_995_, v_a_1012_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v_expr_1015_; lean_object* v___x_1016_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v_expr_1015_ = lean_ctor_get(v_a_1012_, 0);
lean_inc_ref(v_expr_1015_);
lean_dec(v_a_1012_);
v___x_1016_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_1015_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_n(v_a_1017_, 2);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_1014_, v_a_1017_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_expr_1020_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_expr_1020_ = lean_ctor_get(v_a_1017_, 0);
lean_inc_ref(v_expr_1020_);
lean_dec(v_a_1017_);
v___x_1021_ = l_Lean_Meta_Sym_canon(v_expr_1020_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_Meta_Sym_shareCommon(v_a_1022_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1072_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1072_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1072_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_toCold_1042_; lean_object* v_options_1043_; uint8_t v_hasTrace_1044_; 
v_toCold_1042_ = lean_ctor_get(v_a_989_, 0);
v_options_1043_ = lean_ctor_get(v_toCold_1042_, 2);
v_hasTrace_1044_ = lean_ctor_get_uint8(v_options_1043_, sizeof(void*)*1);
if (v_hasTrace_1044_ == 0)
{
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
goto v___jp_1028_;
}
else
{
lean_object* v_inheritedTraceOptions_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_inheritedTraceOptions_1045_ = lean_ctor_get(v_toCold_1042_, 11);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_1047_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_1048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1045_, v_options_1043_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
goto v___jp_1028_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_Grind_updateLastTag(v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref_known(v___x_1049_, 1);
v___x_1050_ = l_Lean_MessageData_ofExpr(v_a_993_);
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
lean_inc(v_a_1024_);
v___x_1053_ = l_Lean_MessageData_ofExpr(v_a_1024_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1046_, v___x_1054_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_dec_ref_known(v___x_1055_, 1);
goto v___jp_1028_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1026_);
lean_dec(v_a_1024_);
lean_dec(v_a_1019_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_del_object(v___x_1026_);
lean_dec(v_a_1024_);
lean_dec(v_a_1019_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
v_a_1064_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1049_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1049_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
v___jp_1028_:
{
lean_object* v_proof_x3f_1029_; uint8_t v_cache_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
v_proof_x3f_1029_ = lean_ctor_get(v_a_1019_, 1);
v_cache_1030_ = lean_ctor_get_uint8(v_a_1019_, sizeof(void*)*2);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_a_1019_, 0);
lean_dec(v_unused_1041_);
v___x_1032_ = v_a_1019_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_proof_x3f_1029_);
lean_dec(v_a_1019_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_a_1024_);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1024_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_proof_x3f_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1039_, sizeof(void*)*2, v_cache_1030_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1035_);
v___x_1037_ = v___x_1026_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1019_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1073_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1023_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1023_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1019_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1081_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1021_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1021_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_dec(v_a_1017_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v___x_1018_;
}
}
else
{
lean_dec(v_a_1014_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v___x_1016_;
}
}
else
{
lean_dec(v_a_1012_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v___x_1013_;
}
}
else
{
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v___x_1011_;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1089_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1009_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1009_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1097_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1007_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1007_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1105_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1005_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1005_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1113_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1003_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1003_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1121_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1001_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1001_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
v_a_1129_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_999_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_999_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = lean_grind_preprocess(v_e_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_1150_, lean_object* v_msg_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_1150_, v_msg_1151_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_1164_, v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
return v_res_1177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1185_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_1186_ = l_Lean_Name_append(v___x_1185_, v___x_1184_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_1200_ = l_Lean_mkConst(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_1201_, lean_object* v_proof_1202_, lean_object* v_generation_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
lean_inc(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc(v_a_1211_);
lean_inc_ref(v_a_1210_);
lean_inc(v_a_1209_);
lean_inc_ref(v_a_1208_);
lean_inc(v_a_1207_);
lean_inc_ref(v_a_1206_);
lean_inc(v_a_1205_);
lean_inc(v_a_1204_);
lean_inc_ref(v_prop_1201_);
v___x_1215_ = lean_grind_preprocess(v_prop_1201_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_expr_1217_; lean_object* v_proof_x3f_1218_; lean_object* v___y_1220_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_expr_1217_ = lean_ctor_get(v_a_1216_, 0);
lean_inc_ref(v_expr_1217_);
v_proof_x3f_1218_ = lean_ctor_get(v_a_1216_, 1);
lean_inc(v_proof_x3f_1218_);
lean_dec(v_a_1216_);
if (lean_obj_tag(v_proof_x3f_1218_) == 1)
{
lean_object* v_val_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_val_1237_ = lean_ctor_get(v_proof_x3f_1218_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_proof_x3f_1218_, 1);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_1217_);
lean_inc_ref(v_prop_1201_);
v___x_1239_ = l_Lean_mkApp4(v___x_1238_, v_prop_1201_, v_expr_1217_, v_val_1237_, v_proof_1202_);
v___y_1220_ = v___x_1239_;
goto v___jp_1219_;
}
else
{
lean_dec(v_proof_x3f_1218_);
v___y_1220_ = v_proof_1202_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v_toCold_1221_; lean_object* v_options_1222_; uint8_t v_hasTrace_1223_; 
v_toCold_1221_ = lean_ctor_get(v_a_1212_, 0);
v_options_1222_ = lean_ctor_get(v_toCold_1221_, 2);
v_hasTrace_1223_ = lean_ctor_get_uint8(v_options_1222_, sizeof(void*)*1);
if (v_hasTrace_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_prop_1201_);
v___x_1224_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1217_, v___y_1220_, v_generation_1203_, v_a_1204_);
return v___x_1224_;
}
else
{
lean_object* v_inheritedTraceOptions_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_inheritedTraceOptions_1225_ = lean_ctor_get(v_toCold_1221_, 11);
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1225_, v_options_1222_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v_prop_1201_);
v___x_1229_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1217_, v___y_1220_, v_generation_1203_, v_a_1204_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = l_Lean_MessageData_ofExpr(v_prop_1201_);
v___x_1231_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_inc_ref(v_expr_1217_);
v___x_1233_ = l_Lean_MessageData_ofExpr(v_expr_1217_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1226_, v___x_1234_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1235_, 1);
v___x_1236_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_expr_1217_, v___y_1220_, v_generation_1203_, v_a_1204_);
return v___x_1236_;
}
else
{
lean_dec_ref(v___y_1220_);
lean_dec_ref(v_expr_1217_);
lean_dec(v_generation_1203_);
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_generation_1203_);
lean_dec_ref(v_proof_1202_);
lean_dec_ref(v_prop_1201_);
v_a_1240_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1215_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1215_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_1248_, lean_object* v_proof_1249_, lean_object* v_generation_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_1248_, v_proof_1249_, v_generation_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec(v_a_1251_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_1263_, lean_object* v_generation_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
lean_inc(v_a_1272_);
lean_inc_ref(v_a_1271_);
lean_inc_ref(v_proof_1263_);
v___x_1276_ = lean_infer_type(v_proof_1263_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_toCold_1277_; lean_object* v_options_1278_; uint8_t v_hasTrace_1279_; 
v_toCold_1277_ = lean_ctor_get(v_a_1273_, 0);
v_options_1278_ = lean_ctor_get(v_toCold_1277_, 2);
v_hasTrace_1279_ = lean_ctor_get_uint8(v_options_1278_, sizeof(void*)*1);
if (v_hasTrace_1279_ == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1281_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1280_, v_proof_1263_, v_generation_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v_inheritedTraceOptions_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_a_1282_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1276_, 1);
v_inheritedTraceOptions_1283_ = lean_ctor_get(v_toCold_1277_, 11);
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1286_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1283_, v_options_1278_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1282_, v_proof_1263_, v_generation_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc(v_a_1282_);
v___x_1288_ = l_Lean_MessageData_ofExpr(v_a_1282_);
v___x_1289_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1284_, v___x_1288_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref_known(v___x_1289_, 1);
v___x_1290_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1282_, v_proof_1263_, v_generation_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1290_;
}
else
{
lean_dec(v_a_1282_);
lean_dec(v_generation_1264_);
lean_dec_ref(v_proof_1263_);
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_generation_1264_);
lean_dec_ref(v_proof_1263_);
v_a_1291_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1276_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1276_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_1299_, lean_object* v_generation_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Grind_pushNewFact(v_proof_1299_, v_generation_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec(v_a_1301_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1326_; 
v___x_1324_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_1313_, v_a_1320_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1325_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_1327_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1329_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = l_Lean_Meta_Grind_foldProjs(v_a_1331_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1333_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = l_Lean_Meta_Sym_canon(v_a_1335_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1338_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = l_Lean_Meta_Sym_shareCommon(v_a_1337_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1338_;
}
else
{
return v___x_1336_;
}
}
else
{
return v___x_1334_;
}
}
else
{
return v___x_1332_;
}
}
else
{
return v___x_1330_;
}
}
else
{
return v___x_1328_;
}
}
else
{
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1351_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Meta_Grind_preprocessLight(v_e_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1376_;
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

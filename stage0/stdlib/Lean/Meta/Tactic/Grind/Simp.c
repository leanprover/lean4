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
uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1_ = stack[0].m_obj;
lean_object* v_opt_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(v_opts_1_, v_opt_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0___boxed(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(v_opts_12_, v_opt_13_);
lean_dec_ref(v_opt_13_);
lean_dec_ref(v_opts_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg(lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_16_);
v___x_19_ = l_Lean_Meta_Grind_backward_grind_normalizer;
v___x_20_ = l_Lean_Option_get___at___00Lean_Meta_Grind_isLegacyNormalizer_spec__0(v___x_18_, v___x_19_);
lean_dec_ref(v___x_18_);
v___x_21_ = lean_box(v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isLegacyNormalizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_16_ = stack[0].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_16_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___redArg___boxed(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_24_);
lean_dec_ref(v_a_24_);
return v_res_26_;
}
}
lean_object* l_Lean_Meta_Grind_isLegacyNormalizer(lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_27_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isLegacyNormalizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_27_ = stack[0].m_obj;
lean_object* v_a_28_ = stack[1].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_Grind_isLegacyNormalizer(v_a_27_, v_a_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isLegacyNormalizer___boxed(lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Grind_isLegacyNormalizer(v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_35_;
}
}
lean_object* l_Lean_Meta_Grind_symNorm(lean_object* v_e_42_, lean_object* v_methods_43_, lean_object* v_dmethods_44_, lean_object* v_s_45_, lean_object* v_ds_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_Grind_foldProjs(v_e_42_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_54_, 1);
v___x_56_ = l_Lean_Meta_Sym_preprocessExpr(v_a_55_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc_n(v_a_57_, 2);
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_58_, 0, v_a_57_);
v___x_59_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__0));
v___x_60_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_58_, v_methods_43_, v___x_59_, v_s_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_107_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_107_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_107_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_107_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_fst_65_; lean_object* v_snd_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_106_; 
v_fst_65_ = lean_ctor_get(v_a_61_, 0);
v_snd_66_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_106_ == 0)
{
v___x_68_ = v_a_61_;
v_isShared_69_ = v_isSharedCheck_106_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_snd_66_);
lean_inc(v_fst_65_);
lean_dec(v_a_61_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_106_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___y_71_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v_fst_84_; lean_object* v_snd_85_; 
if (lean_obj_tag(v_fst_65_) == 0)
{
lean_object* v___x_102_; 
lean_dec_ref_known(v_fst_65_, 0);
v___x_102_ = lean_box(0);
v_fst_84_ = v_a_57_;
v_snd_85_ = v___x_102_;
goto v___jp_83_;
}
else
{
lean_object* v_e_x27_103_; lean_object* v_proof_104_; lean_object* v___x_105_; 
lean_dec(v_a_57_);
v_e_x27_103_ = lean_ctor_get(v_fst_65_, 0);
lean_inc_ref(v_e_x27_103_);
v_proof_104_ = lean_ctor_get(v_fst_65_, 1);
lean_inc_ref(v_proof_104_);
lean_dec_ref_known(v_fst_65_, 2);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_proof_104_);
v_fst_84_ = v_e_x27_103_;
v_snd_85_ = v___x_105_;
goto v___jp_83_;
}
v___jp_70_:
{
uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = 1;
v___x_75_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___y_72_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*2, v___x_74_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___y_71_);
lean_ctor_set(v___x_68_, 0, v_snd_66_);
v___x_77_ = v___x_68_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_snd_66_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___y_71_);
v___x_77_ = v_reuseFailAlloc_82_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_78_);
v___x_80_ = v___x_63_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
v___jp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_inc_ref(v_fst_84_);
v___x_86_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_86_, 0, v_fst_84_);
v___x_87_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
v___x_88_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_86_, v_dmethods_44_, v___x_87_, v_ds_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v_fst_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
v_fst_90_ = lean_ctor_get(v_a_89_, 0);
if (lean_obj_tag(v_fst_90_) == 0)
{
lean_object* v_snd_91_; 
v_snd_91_ = lean_ctor_get(v_a_89_, 1);
lean_inc(v_snd_91_);
lean_dec(v_a_89_);
v___y_71_ = v_snd_91_;
v___y_72_ = v_snd_85_;
v___y_73_ = v_fst_84_;
goto v___jp_70_;
}
else
{
lean_object* v_snd_92_; lean_object* v_e_x27_93_; 
lean_inc_ref(v_fst_90_);
lean_dec_ref(v_fst_84_);
v_snd_92_ = lean_ctor_get(v_a_89_, 1);
lean_inc(v_snd_92_);
lean_dec(v_a_89_);
v_e_x27_93_ = lean_ctor_get(v_fst_90_, 0);
lean_inc_ref(v_e_x27_93_);
lean_dec_ref_known(v_fst_90_, 1);
v___y_71_ = v_snd_92_;
v___y_72_ = v_snd_85_;
v___y_73_ = v_e_x27_93_;
goto v___jp_70_;
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_snd_85_);
lean_dec_ref(v_fst_84_);
lean_del_object(v___x_68_);
lean_dec(v_snd_66_);
lean_del_object(v___x_63_);
v_a_94_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_88_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_88_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec(v_a_57_);
lean_dec_ref(v_ds_46_);
lean_dec_ref(v_dmethods_44_);
v_a_108_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_60_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_60_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_ds_46_);
lean_dec_ref(v_s_45_);
lean_dec_ref(v_dmethods_44_);
lean_dec_ref(v_methods_43_);
v_a_116_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_56_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_56_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v_ds_46_);
lean_dec_ref(v_s_45_);
lean_dec_ref(v_dmethods_44_);
lean_dec_ref(v_methods_43_);
v_a_124_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_54_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_54_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_symNorm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_42_ = stack[0].m_obj;
lean_object* v_methods_43_ = stack[1].m_obj;
lean_object* v_dmethods_44_ = stack[2].m_obj;
lean_object* v_s_45_ = stack[3].m_obj;
lean_object* v_ds_46_ = stack[4].m_obj;
lean_object* v_a_47_ = stack[5].m_obj;
lean_object* v_a_48_ = stack[6].m_obj;
lean_object* v_a_49_ = stack[7].m_obj;
lean_object* v_a_50_ = stack[8].m_obj;
lean_object* v_a_51_ = stack[9].m_obj;
lean_object* v_a_52_ = stack[10].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Meta_Grind_symNorm(v_e_42_, v_methods_43_, v_dmethods_44_, v_s_45_, v_ds_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_symNorm___boxed(lean_object* v_e_133_, lean_object* v_methods_134_, lean_object* v_dmethods_135_, lean_object* v_s_136_, lean_object* v_ds_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Grind_symNorm(v_e_133_, v_methods_134_, v_dmethods_135_, v_s_136_, v_ds_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_145_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(lean_object* v_category_146_, lean_object* v_opts_147_, lean_object* v_act_148_, lean_object* v_decl_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
lean_inc(v___y_156_);
lean_inc_ref(v___y_155_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
v___x_160_ = lean_apply_9(v_act_148_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
v___x_161_ = l_Lean_profileitIOUnsafe___redArg(v_category_146_, v_opts_147_, v___x_160_, v_decl_149_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_146_ = stack[0].m_obj;
lean_object* v_opts_147_ = stack[1].m_obj;
lean_object* v_act_148_ = stack[2].m_obj;
lean_object* v_decl_149_ = stack[3].m_obj;
lean_object* v___y_150_ = stack[4].m_obj;
lean_object* v___y_151_ = stack[5].m_obj;
lean_object* v___y_152_ = stack[6].m_obj;
lean_object* v___y_153_ = stack[7].m_obj;
lean_object* v___y_154_ = stack[8].m_obj;
lean_object* v___y_155_ = stack[9].m_obj;
lean_object* v___y_156_ = stack[10].m_obj;
lean_object* v___y_157_ = stack[11].m_obj;
lean_object* v___y_158_ = stack[12].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v_category_146_, v_opts_147_, v_act_148_, v_decl_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg___boxed(lean_object* v_category_163_, lean_object* v_opts_164_, lean_object* v_act_165_, lean_object* v_decl_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v_category_163_, v_opts_164_, v_act_165_, v_decl_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v_opts_164_);
lean_dec_ref(v_category_163_);
return v_res_177_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_category_179_, lean_object* v_opts_180_, lean_object* v_act_181_, lean_object* v_decl_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v_category_179_, v_opts_180_, v_act_181_, v_decl_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_179_ = stack[1].m_obj;
lean_object* v_opts_180_ = stack[2].m_obj;
lean_object* v_act_181_ = stack[3].m_obj;
lean_object* v_decl_182_ = stack[4].m_obj;
lean_object* v___y_183_ = stack[5].m_obj;
lean_object* v___y_184_ = stack[6].m_obj;
lean_object* v___y_185_ = stack[7].m_obj;
lean_object* v___y_186_ = stack[8].m_obj;
lean_object* v___y_187_ = stack[9].m_obj;
lean_object* v___y_188_ = stack[10].m_obj;
lean_object* v___y_189_ = stack[11].m_obj;
lean_object* v___y_190_ = stack[12].m_obj;
lean_object* v___y_191_ = stack[13].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(lean_box(0), v_category_179_, v_opts_180_, v_act_181_, v_decl_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___boxed(lean_object* v_00_u03b1_195_, lean_object* v_category_196_, lean_object* v_opts_197_, lean_object* v_act_198_, lean_object* v_decl_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0(v_00_u03b1_195_, v_category_196_, v_opts_197_, v_act_198_, v_decl_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v_opts_197_);
lean_dec_ref(v_category_196_);
return v_res_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_214_);
lean_ctor_set(v___x_216_, 3, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__1);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
return v___x_219_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(lean_object* v_e_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_congrThms_232_; lean_object* v_simp_233_; lean_object* v_symSimp_234_; lean_object* v_symDSimp_235_; lean_object* v_lastTag_236_; lean_object* v_counters_237_; lean_object* v_splitDiags_238_; lean_object* v_ematchDiags_239_; lean_object* v_lawfulEqCmpMap_240_; lean_object* v_reflCmpMap_241_; lean_object* v_anchors_242_; lean_object* v_instanceMap_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_297_; 
v___x_231_ = lean_st_ref_take(v___y_223_);
v_congrThms_232_ = lean_ctor_get(v___x_231_, 0);
v_simp_233_ = lean_ctor_get(v___x_231_, 1);
v_symSimp_234_ = lean_ctor_get(v___x_231_, 2);
v_symDSimp_235_ = lean_ctor_get(v___x_231_, 3);
v_lastTag_236_ = lean_ctor_get(v___x_231_, 4);
v_counters_237_ = lean_ctor_get(v___x_231_, 5);
v_splitDiags_238_ = lean_ctor_get(v___x_231_, 6);
v_ematchDiags_239_ = lean_ctor_get(v___x_231_, 7);
v_lawfulEqCmpMap_240_ = lean_ctor_get(v___x_231_, 8);
v_reflCmpMap_241_ = lean_ctor_get(v___x_231_, 9);
v_anchors_242_ = lean_ctor_get(v___x_231_, 10);
v_instanceMap_243_ = lean_ctor_get(v___x_231_, 11);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_297_ == 0)
{
v___x_245_ = v___x_231_;
v_isShared_246_ = v_isSharedCheck_297_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_instanceMap_243_);
lean_inc(v_anchors_242_);
lean_inc(v_reflCmpMap_241_);
lean_inc(v_lawfulEqCmpMap_240_);
lean_inc(v_ematchDiags_239_);
lean_inc(v_splitDiags_238_);
lean_inc(v_counters_237_);
lean_inc(v_lastTag_236_);
lean_inc(v_symDSimp_235_);
lean_inc(v_symSimp_234_);
lean_inc(v_simp_233_);
lean_inc(v_congrThms_232_);
lean_dec(v___x_231_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_297_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2);
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 3, v___x_248_);
lean_ctor_set(v___x_245_, 2, v___x_247_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_congrThms_232_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_simp_233_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_lastTag_236_);
lean_ctor_set(v_reuseFailAlloc_296_, 5, v_counters_237_);
lean_ctor_set(v_reuseFailAlloc_296_, 6, v_splitDiags_238_);
lean_ctor_set(v_reuseFailAlloc_296_, 7, v_ematchDiags_239_);
lean_ctor_set(v_reuseFailAlloc_296_, 8, v_lawfulEqCmpMap_240_);
lean_ctor_set(v_reuseFailAlloc_296_, 9, v_reflCmpMap_241_);
lean_ctor_set(v_reuseFailAlloc_296_, 10, v_anchors_242_);
lean_ctor_set(v_reuseFailAlloc_296_, 11, v_instanceMap_243_);
v___x_250_ = v_reuseFailAlloc_296_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v_symSimpMethods_252_; lean_object* v_symDSimpMethods_253_; lean_object* v___x_254_; 
v___x_251_ = lean_st_ref_put(v___y_223_, v___x_250_);
v_symSimpMethods_252_ = lean_ctor_get(v___y_222_, 2);
v_symDSimpMethods_253_ = lean_ctor_get(v___y_222_, 3);
lean_inc_ref(v_symDSimpMethods_253_);
lean_inc_ref(v_symSimpMethods_252_);
v___x_254_ = l_Lean_Meta_Grind_symNorm(v_e_220_, v_symSimpMethods_252_, v_symDSimpMethods_253_, v_symSimp_234_, v_symDSimp_235_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_287_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_287_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_287_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_287_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_snd_259_; lean_object* v_fst_260_; lean_object* v_fst_261_; lean_object* v_snd_262_; lean_object* v___x_263_; lean_object* v_congrThms_264_; lean_object* v_simp_265_; lean_object* v_lastTag_266_; lean_object* v_counters_267_; lean_object* v_splitDiags_268_; lean_object* v_ematchDiags_269_; lean_object* v_lawfulEqCmpMap_270_; lean_object* v_reflCmpMap_271_; lean_object* v_anchors_272_; lean_object* v_instanceMap_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_snd_259_ = lean_ctor_get(v_a_255_, 1);
lean_inc(v_snd_259_);
v_fst_260_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_fst_260_);
lean_dec(v_a_255_);
v_fst_261_ = lean_ctor_get(v_snd_259_, 0);
lean_inc(v_fst_261_);
v_snd_262_ = lean_ctor_get(v_snd_259_, 1);
lean_inc(v_snd_262_);
lean_dec(v_snd_259_);
v___x_263_ = lean_st_ref_take(v___y_223_);
v_congrThms_264_ = lean_ctor_get(v___x_263_, 0);
v_simp_265_ = lean_ctor_get(v___x_263_, 1);
v_lastTag_266_ = lean_ctor_get(v___x_263_, 4);
v_counters_267_ = lean_ctor_get(v___x_263_, 5);
v_splitDiags_268_ = lean_ctor_get(v___x_263_, 6);
v_ematchDiags_269_ = lean_ctor_get(v___x_263_, 7);
v_lawfulEqCmpMap_270_ = lean_ctor_get(v___x_263_, 8);
v_reflCmpMap_271_ = lean_ctor_get(v___x_263_, 9);
v_anchors_272_ = lean_ctor_get(v___x_263_, 10);
v_instanceMap_273_ = lean_ctor_get(v___x_263_, 11);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; 
v_unused_285_ = lean_ctor_get(v___x_263_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v___x_263_, 2);
lean_dec(v_unused_286_);
v___x_275_ = v___x_263_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_instanceMap_273_);
lean_inc(v_anchors_272_);
lean_inc(v_reflCmpMap_271_);
lean_inc(v_lawfulEqCmpMap_270_);
lean_inc(v_ematchDiags_269_);
lean_inc(v_splitDiags_268_);
lean_inc(v_counters_267_);
lean_inc(v_lastTag_266_);
lean_inc(v_simp_265_);
lean_inc(v_congrThms_264_);
lean_dec(v___x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 3, v_snd_262_);
lean_ctor_set(v___x_275_, 2, v_fst_261_);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_congrThms_264_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_simp_265_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_fst_261_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_snd_262_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_lastTag_266_);
lean_ctor_set(v_reuseFailAlloc_283_, 5, v_counters_267_);
lean_ctor_set(v_reuseFailAlloc_283_, 6, v_splitDiags_268_);
lean_ctor_set(v_reuseFailAlloc_283_, 7, v_ematchDiags_269_);
lean_ctor_set(v_reuseFailAlloc_283_, 8, v_lawfulEqCmpMap_270_);
lean_ctor_set(v_reuseFailAlloc_283_, 9, v_reflCmpMap_271_);
lean_ctor_set(v_reuseFailAlloc_283_, 10, v_anchors_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 11, v_instanceMap_273_);
v___x_278_ = v_reuseFailAlloc_283_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = lean_st_ref_put(v___y_223_, v___x_278_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_fst_260_);
v___x_281_ = v___x_257_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_fst_260_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_a_288_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_254_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_254_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_220_ = stack[0].m_obj;
lean_object* v___y_221_ = stack[1].m_obj;
lean_object* v___y_222_ = stack[2].m_obj;
lean_object* v___y_223_ = stack[3].m_obj;
lean_object* v___y_224_ = stack[4].m_obj;
lean_object* v___y_225_ = stack[5].m_obj;
lean_object* v___y_226_ = stack[6].m_obj;
lean_object* v___y_227_ = stack[7].m_obj;
lean_object* v___y_228_ = stack[8].m_obj;
lean_object* v___y_229_ = stack[9].m_obj;
lean_object* v_res_298_;
v_res_298_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(v_e_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed(lean_object* v_e_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(v_e_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
return v_res_310_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_323_, 0, v_e_312_);
v___x_324_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_320_);
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_326_ = lean_box(0);
v___x_327_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_325_, v___x_324_, v___f_323_, v___x_326_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec_ref(v___x_324_);
return v___x_327_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_312_ = stack[0].m_obj;
lean_object* v_a_313_ = stack[1].m_obj;
lean_object* v_a_314_ = stack[2].m_obj;
lean_object* v_a_315_ = stack[3].m_obj;
lean_object* v_a_316_ = stack[4].m_obj;
lean_object* v_a_317_ = stack[5].m_obj;
lean_object* v_a_318_ = stack[6].m_obj;
lean_object* v_a_319_ = stack[7].m_obj;
lean_object* v_a_320_ = stack[8].m_obj;
lean_object* v_a_321_ = stack[9].m_obj;
lean_object* v_res_328_;
v_res_328_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
stack->m_obj
 = v_res_328_;
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
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(lean_object* v_e_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
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
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v_congrThms_362_; lean_object* v_simp_363_; lean_object* v_symSimp_364_; lean_object* v_symDSimp_365_; lean_object* v_lastTag_366_; lean_object* v_counters_367_; lean_object* v_splitDiags_368_; lean_object* v_ematchDiags_369_; lean_object* v_lawfulEqCmpMap_370_; lean_object* v_reflCmpMap_371_; lean_object* v_anchors_372_; lean_object* v_instanceMap_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_429_; 
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
v_instanceMap_373_ = lean_ctor_get(v___x_361_, 11);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_429_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_429_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_instanceMap_373_);
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
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_429_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 3, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_congrThms_362_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_simp_363_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_symSimp_364_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_lastTag_366_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_counters_367_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_splitDiags_368_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v_ematchDiags_369_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_lawfulEqCmpMap_370_);
lean_ctor_set(v_reuseFailAlloc_428_, 9, v_reflCmpMap_371_);
lean_ctor_set(v_reuseFailAlloc_428_, 10, v_anchors_372_);
lean_ctor_set(v_reuseFailAlloc_428_, 11, v_instanceMap_373_);
v___x_379_ = v_reuseFailAlloc_428_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v_symDSimpMethods_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_380_ = lean_st_ref_put(v___y_349_, v___x_379_);
v_symDSimpMethods_381_ = lean_ctor_get(v___y_348_, 3);
lean_inc(v_a_360_);
v___x_382_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_382_, 0, v_a_360_);
v___x_383_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
lean_inc_ref(v_symDSimpMethods_381_);
v___x_384_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_382_, v_symDSimpMethods_381_, v___x_383_, v_symDSimp_365_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_419_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_419_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_419_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_419_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; lean_object* v_congrThms_392_; lean_object* v_simp_393_; lean_object* v_symSimp_394_; lean_object* v_lastTag_395_; lean_object* v_counters_396_; lean_object* v_splitDiags_397_; lean_object* v_ematchDiags_398_; lean_object* v_lawfulEqCmpMap_399_; lean_object* v_reflCmpMap_400_; lean_object* v_anchors_401_; lean_object* v_instanceMap_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_417_; 
v_fst_389_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_a_385_, 1);
lean_inc(v_snd_390_);
lean_dec(v_a_385_);
v___x_391_ = lean_st_ref_take(v___y_349_);
v_congrThms_392_ = lean_ctor_get(v___x_391_, 0);
v_simp_393_ = lean_ctor_get(v___x_391_, 1);
v_symSimp_394_ = lean_ctor_get(v___x_391_, 2);
v_lastTag_395_ = lean_ctor_get(v___x_391_, 4);
v_counters_396_ = lean_ctor_get(v___x_391_, 5);
v_splitDiags_397_ = lean_ctor_get(v___x_391_, 6);
v_ematchDiags_398_ = lean_ctor_get(v___x_391_, 7);
v_lawfulEqCmpMap_399_ = lean_ctor_get(v___x_391_, 8);
v_reflCmpMap_400_ = lean_ctor_get(v___x_391_, 9);
v_anchors_401_ = lean_ctor_get(v___x_391_, 10);
v_instanceMap_402_ = lean_ctor_get(v___x_391_, 11);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_391_, 3);
lean_dec(v_unused_418_);
v___x_404_ = v___x_391_;
v_isShared_405_ = v_isSharedCheck_417_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_instanceMap_402_);
lean_inc(v_anchors_401_);
lean_inc(v_reflCmpMap_400_);
lean_inc(v_lawfulEqCmpMap_399_);
lean_inc(v_ematchDiags_398_);
lean_inc(v_splitDiags_397_);
lean_inc(v_counters_396_);
lean_inc(v_lastTag_395_);
lean_inc(v_symSimp_394_);
lean_inc(v_simp_393_);
lean_inc(v_congrThms_392_);
lean_dec(v___x_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_417_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 3, v_snd_390_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_congrThms_392_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_simp_393_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_symSimp_394_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_snd_390_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v_lastTag_395_);
lean_ctor_set(v_reuseFailAlloc_416_, 5, v_counters_396_);
lean_ctor_set(v_reuseFailAlloc_416_, 6, v_splitDiags_397_);
lean_ctor_set(v_reuseFailAlloc_416_, 7, v_ematchDiags_398_);
lean_ctor_set(v_reuseFailAlloc_416_, 8, v_lawfulEqCmpMap_399_);
lean_ctor_set(v_reuseFailAlloc_416_, 9, v_reflCmpMap_400_);
lean_ctor_set(v_reuseFailAlloc_416_, 10, v_anchors_401_);
lean_ctor_set(v_reuseFailAlloc_416_, 11, v_instanceMap_402_);
v___x_407_ = v_reuseFailAlloc_416_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; 
v___x_408_ = lean_st_ref_put(v___y_349_, v___x_407_);
if (lean_obj_tag(v_fst_389_) == 0)
{
lean_object* v___x_410_; 
lean_dec_ref_known(v_fst_389_, 0);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_a_360_);
v___x_410_ = v___x_387_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_360_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v_e_x27_412_; lean_object* v___x_414_; 
lean_dec(v_a_360_);
v_e_x27_412_ = lean_ctor_get(v_fst_389_, 0);
lean_inc_ref(v_e_x27_412_);
lean_dec_ref_known(v_fst_389_, 1);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_e_x27_412_);
v___x_414_ = v___x_387_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_e_x27_412_);
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
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_a_360_);
v_a_420_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_384_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_384_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_346_ = stack[0].m_obj;
lean_object* v___y_347_ = stack[1].m_obj;
lean_object* v___y_348_ = stack[2].m_obj;
lean_object* v___y_349_ = stack[3].m_obj;
lean_object* v___y_350_ = stack[4].m_obj;
lean_object* v___y_351_ = stack[5].m_obj;
lean_object* v___y_352_ = stack[6].m_obj;
lean_object* v___y_353_ = stack[7].m_obj;
lean_object* v___y_354_ = stack[8].m_obj;
lean_object* v___y_355_ = stack[9].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(v_e_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(v_e_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
return v_res_442_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(lean_object* v_e_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___f_455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_455_, 0, v_e_444_);
v___x_456_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_452_);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_457_, v___x_456_, v___f_455_, v___x_458_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec_ref(v___x_456_);
return v___x_459_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_444_ = stack[0].m_obj;
lean_object* v_a_445_ = stack[1].m_obj;
lean_object* v_a_446_ = stack[2].m_obj;
lean_object* v_a_447_ = stack[3].m_obj;
lean_object* v_a_448_ = stack[4].m_obj;
lean_object* v_a_449_ = stack[5].m_obj;
lean_object* v_a_450_ = stack[6].m_obj;
lean_object* v_a_451_ = stack[7].m_obj;
lean_object* v_a_452_ = stack[8].m_obj;
lean_object* v_a_453_ = stack[9].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___boxed(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
return v_res_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_unsigned_to_nat(16u);
v___x_475_ = lean_mk_array(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_483_ = 1;
v___x_484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_481_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*2, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(32u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6(void){
_start:
{
size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = ((size_t)5ULL);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_unsigned_to_nat(32u);
v___x_494_ = lean_mk_empty_array_with_capacity(v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5);
v___x_496_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_492_);
lean_ctor_set(v___x_496_, 3, v___x_492_);
lean_ctor_set_usize(v___x_496_, 4, v___x_491_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6);
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
lean_ctor_set(v___x_499_, 3, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4);
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3);
v___x_505_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_503_);
lean_ctor_set(v___x_505_, 3, v___x_502_);
lean_ctor_set(v___x_505_, 4, v___x_501_);
lean_ctor_set(v___x_505_, 5, v___x_500_);
return v___x_505_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(lean_object* v_e_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_congrThms_518_; lean_object* v_simp_519_; lean_object* v_symSimp_520_; lean_object* v_symDSimp_521_; lean_object* v_lastTag_522_; lean_object* v_counters_523_; lean_object* v_splitDiags_524_; lean_object* v_ematchDiags_525_; lean_object* v_lawfulEqCmpMap_526_; lean_object* v_reflCmpMap_527_; lean_object* v_anchors_528_; lean_object* v_instanceMap_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_580_; 
v___x_517_ = lean_st_ref_take(v___y_509_);
v_congrThms_518_ = lean_ctor_get(v___x_517_, 0);
v_simp_519_ = lean_ctor_get(v___x_517_, 1);
v_symSimp_520_ = lean_ctor_get(v___x_517_, 2);
v_symDSimp_521_ = lean_ctor_get(v___x_517_, 3);
v_lastTag_522_ = lean_ctor_get(v___x_517_, 4);
v_counters_523_ = lean_ctor_get(v___x_517_, 5);
v_splitDiags_524_ = lean_ctor_get(v___x_517_, 6);
v_ematchDiags_525_ = lean_ctor_get(v___x_517_, 7);
v_lawfulEqCmpMap_526_ = lean_ctor_get(v___x_517_, 8);
v_reflCmpMap_527_ = lean_ctor_get(v___x_517_, 9);
v_anchors_528_ = lean_ctor_get(v___x_517_, 10);
v_instanceMap_529_ = lean_ctor_get(v___x_517_, 11);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_580_ == 0)
{
v___x_531_ = v___x_517_;
v_isShared_532_ = v_isSharedCheck_580_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_instanceMap_529_);
lean_inc(v_anchors_528_);
lean_inc(v_reflCmpMap_527_);
lean_inc(v_lawfulEqCmpMap_526_);
lean_inc(v_ematchDiags_525_);
lean_inc(v_splitDiags_524_);
lean_inc(v_counters_523_);
lean_inc(v_lastTag_522_);
lean_inc(v_symDSimp_521_);
lean_inc(v_symSimp_520_);
lean_inc(v_simp_519_);
lean_inc(v_congrThms_518_);
lean_dec(v___x_517_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_580_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_congrThms_518_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_symSimp_520_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_symDSimp_521_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_lastTag_522_);
lean_ctor_set(v_reuseFailAlloc_579_, 5, v_counters_523_);
lean_ctor_set(v_reuseFailAlloc_579_, 6, v_splitDiags_524_);
lean_ctor_set(v_reuseFailAlloc_579_, 7, v_ematchDiags_525_);
lean_ctor_set(v_reuseFailAlloc_579_, 8, v_lawfulEqCmpMap_526_);
lean_ctor_set(v_reuseFailAlloc_579_, 9, v_reflCmpMap_527_);
lean_ctor_set(v_reuseFailAlloc_579_, 10, v_anchors_528_);
lean_ctor_set(v_reuseFailAlloc_579_, 11, v_instanceMap_529_);
v___x_535_ = v_reuseFailAlloc_579_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v_simp_537_; lean_object* v_simpMethods_538_; lean_object* v___x_539_; 
v___x_536_ = lean_st_ref_put(v___y_509_, v___x_535_);
v_simp_537_ = lean_ctor_get(v___y_508_, 0);
v_simpMethods_538_ = lean_ctor_get(v___y_508_, 1);
lean_inc_ref(v_simpMethods_538_);
lean_inc_ref(v_simp_537_);
v___x_539_ = l_Lean_Meta_Simp_mainCore(v_e_506_, v_simp_537_, v_simp_519_, v_simpMethods_538_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_570_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_570_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_570_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_570_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_546_; lean_object* v_congrThms_547_; lean_object* v_symSimp_548_; lean_object* v_symDSimp_549_; lean_object* v_lastTag_550_; lean_object* v_counters_551_; lean_object* v_splitDiags_552_; lean_object* v_ematchDiags_553_; lean_object* v_lawfulEqCmpMap_554_; lean_object* v_reflCmpMap_555_; lean_object* v_anchors_556_; lean_object* v_instanceMap_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_568_; 
v_fst_544_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v_a_540_, 1);
lean_inc(v_snd_545_);
lean_dec(v_a_540_);
v___x_546_ = lean_st_ref_take(v___y_509_);
v_congrThms_547_ = lean_ctor_get(v___x_546_, 0);
v_symSimp_548_ = lean_ctor_get(v___x_546_, 2);
v_symDSimp_549_ = lean_ctor_get(v___x_546_, 3);
v_lastTag_550_ = lean_ctor_get(v___x_546_, 4);
v_counters_551_ = lean_ctor_get(v___x_546_, 5);
v_splitDiags_552_ = lean_ctor_get(v___x_546_, 6);
v_ematchDiags_553_ = lean_ctor_get(v___x_546_, 7);
v_lawfulEqCmpMap_554_ = lean_ctor_get(v___x_546_, 8);
v_reflCmpMap_555_ = lean_ctor_get(v___x_546_, 9);
v_anchors_556_ = lean_ctor_get(v___x_546_, 10);
v_instanceMap_557_ = lean_ctor_get(v___x_546_, 11);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_546_, 1);
lean_dec(v_unused_569_);
v___x_559_ = v___x_546_;
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_instanceMap_557_);
lean_inc(v_anchors_556_);
lean_inc(v_reflCmpMap_555_);
lean_inc(v_lawfulEqCmpMap_554_);
lean_inc(v_ematchDiags_553_);
lean_inc(v_splitDiags_552_);
lean_inc(v_counters_551_);
lean_inc(v_lastTag_550_);
lean_inc(v_symDSimp_549_);
lean_inc(v_symSimp_548_);
lean_inc(v_congrThms_547_);
lean_dec(v___x_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v_snd_545_);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_congrThms_547_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_545_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_symSimp_548_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_symDSimp_549_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_lastTag_550_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v_counters_551_);
lean_ctor_set(v_reuseFailAlloc_567_, 6, v_splitDiags_552_);
lean_ctor_set(v_reuseFailAlloc_567_, 7, v_ematchDiags_553_);
lean_ctor_set(v_reuseFailAlloc_567_, 8, v_lawfulEqCmpMap_554_);
lean_ctor_set(v_reuseFailAlloc_567_, 9, v_reflCmpMap_555_);
lean_ctor_set(v_reuseFailAlloc_567_, 10, v_anchors_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 11, v_instanceMap_557_);
v___x_562_ = v_reuseFailAlloc_567_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_st_ref_put(v___y_509_, v___x_562_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_fst_544_);
v___x_565_ = v___x_542_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_544_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_571_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_539_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_539_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_506_ = stack[0].m_obj;
lean_object* v___y_507_ = stack[1].m_obj;
lean_object* v___y_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v___y_512_ = stack[6].m_obj;
lean_object* v___y_513_ = stack[7].m_obj;
lean_object* v___y_514_ = stack[8].m_obj;
lean_object* v___y_515_ = stack[9].m_obj;
lean_object* v_res_581_;
v_res_581_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(v_e_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed(lean_object* v_e_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(v_e_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
return v_res_593_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___f_605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_605_, 0, v_e_594_);
v___x_606_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_602_);
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_608_ = lean_box(0);
v___x_609_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_607_, v___x_606_, v___f_605_, v___x_608_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec_ref(v___x_606_);
return v___x_609_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_594_ = stack[0].m_obj;
lean_object* v_a_595_ = stack[1].m_obj;
lean_object* v_a_596_ = stack[2].m_obj;
lean_object* v_a_597_ = stack[3].m_obj;
lean_object* v_a_598_ = stack[4].m_obj;
lean_object* v_a_599_ = stack[5].m_obj;
lean_object* v_a_600_ = stack[6].m_obj;
lean_object* v_a_601_ = stack[7].m_obj;
lean_object* v_a_602_ = stack[8].m_obj;
lean_object* v_a_603_ = stack[9].m_obj;
lean_object* v_res_610_;
v_res_610_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___boxed(lean_object* v_e_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
return v_res_622_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(lean_object* v_e_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v_congrThms_635_; lean_object* v_simp_636_; lean_object* v_symSimp_637_; lean_object* v_symDSimp_638_; lean_object* v_lastTag_639_; lean_object* v_counters_640_; lean_object* v_splitDiags_641_; lean_object* v_ematchDiags_642_; lean_object* v_lawfulEqCmpMap_643_; lean_object* v_reflCmpMap_644_; lean_object* v_anchors_645_; lean_object* v_instanceMap_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_699_; 
v___x_634_ = lean_st_ref_take(v___y_626_);
v_congrThms_635_ = lean_ctor_get(v___x_634_, 0);
v_simp_636_ = lean_ctor_get(v___x_634_, 1);
v_symSimp_637_ = lean_ctor_get(v___x_634_, 2);
v_symDSimp_638_ = lean_ctor_get(v___x_634_, 3);
v_lastTag_639_ = lean_ctor_get(v___x_634_, 4);
v_counters_640_ = lean_ctor_get(v___x_634_, 5);
v_splitDiags_641_ = lean_ctor_get(v___x_634_, 6);
v_ematchDiags_642_ = lean_ctor_get(v___x_634_, 7);
v_lawfulEqCmpMap_643_ = lean_ctor_get(v___x_634_, 8);
v_reflCmpMap_644_ = lean_ctor_get(v___x_634_, 9);
v_anchors_645_ = lean_ctor_get(v___x_634_, 10);
v_instanceMap_646_ = lean_ctor_get(v___x_634_, 11);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_699_ == 0)
{
v___x_648_ = v___x_634_;
v_isShared_649_ = v_isSharedCheck_699_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_instanceMap_646_);
lean_inc(v_anchors_645_);
lean_inc(v_reflCmpMap_644_);
lean_inc(v_lawfulEqCmpMap_643_);
lean_inc(v_ematchDiags_642_);
lean_inc(v_splitDiags_641_);
lean_inc(v_counters_640_);
lean_inc(v_lastTag_639_);
lean_inc(v_symDSimp_638_);
lean_inc(v_symSimp_637_);
lean_inc(v_simp_636_);
lean_inc(v_congrThms_635_);
lean_dec(v___x_634_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_699_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_650_ = lean_unsigned_to_nat(32u);
v___x_651_ = lean_mk_empty_array_with_capacity(v___x_650_);
lean_dec_ref(v___x_651_);
v___x_652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_652_);
v___x_654_ = v___x_648_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_congrThms_635_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_symSimp_637_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_symDSimp_638_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_lastTag_639_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_counters_640_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_splitDiags_641_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_ematchDiags_642_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_lawfulEqCmpMap_643_);
lean_ctor_set(v_reuseFailAlloc_698_, 9, v_reflCmpMap_644_);
lean_ctor_set(v_reuseFailAlloc_698_, 10, v_anchors_645_);
lean_ctor_set(v_reuseFailAlloc_698_, 11, v_instanceMap_646_);
v___x_654_ = v_reuseFailAlloc_698_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v_simp_656_; lean_object* v_simpMethods_657_; lean_object* v___x_658_; 
v___x_655_ = lean_st_ref_put(v___y_626_, v___x_654_);
v_simp_656_ = lean_ctor_get(v___y_625_, 0);
v_simpMethods_657_ = lean_ctor_get(v___y_625_, 1);
lean_inc_ref(v_simpMethods_657_);
lean_inc_ref(v_simp_656_);
v___x_658_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_623_, v_simp_656_, v_simp_636_, v_simpMethods_657_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_689_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_689_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_689_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_689_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_665_; lean_object* v_congrThms_666_; lean_object* v_symSimp_667_; lean_object* v_symDSimp_668_; lean_object* v_lastTag_669_; lean_object* v_counters_670_; lean_object* v_splitDiags_671_; lean_object* v_ematchDiags_672_; lean_object* v_lawfulEqCmpMap_673_; lean_object* v_reflCmpMap_674_; lean_object* v_anchors_675_; lean_object* v_instanceMap_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_687_; 
v_fst_663_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_664_);
lean_dec(v_a_659_);
v___x_665_ = lean_st_ref_take(v___y_626_);
v_congrThms_666_ = lean_ctor_get(v___x_665_, 0);
v_symSimp_667_ = lean_ctor_get(v___x_665_, 2);
v_symDSimp_668_ = lean_ctor_get(v___x_665_, 3);
v_lastTag_669_ = lean_ctor_get(v___x_665_, 4);
v_counters_670_ = lean_ctor_get(v___x_665_, 5);
v_splitDiags_671_ = lean_ctor_get(v___x_665_, 6);
v_ematchDiags_672_ = lean_ctor_get(v___x_665_, 7);
v_lawfulEqCmpMap_673_ = lean_ctor_get(v___x_665_, 8);
v_reflCmpMap_674_ = lean_ctor_get(v___x_665_, 9);
v_anchors_675_ = lean_ctor_get(v___x_665_, 10);
v_instanceMap_676_ = lean_ctor_get(v___x_665_, 11);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_665_, 1);
lean_dec(v_unused_688_);
v___x_678_ = v___x_665_;
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_instanceMap_676_);
lean_inc(v_anchors_675_);
lean_inc(v_reflCmpMap_674_);
lean_inc(v_lawfulEqCmpMap_673_);
lean_inc(v_ematchDiags_672_);
lean_inc(v_splitDiags_671_);
lean_inc(v_counters_670_);
lean_inc(v_lastTag_669_);
lean_inc(v_symDSimp_668_);
lean_inc(v_symSimp_667_);
lean_inc(v_congrThms_666_);
lean_dec(v___x_665_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v_snd_664_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_congrThms_666_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_snd_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_symSimp_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_symDSimp_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_lastTag_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_counters_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_splitDiags_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v_ematchDiags_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_lawfulEqCmpMap_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_reflCmpMap_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_anchors_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_instanceMap_676_);
v___x_681_ = v_reuseFailAlloc_686_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_put(v___y_626_, v___x_681_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_fst_663_);
v___x_684_ = v___x_661_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_663_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_658_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_658_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_623_ = stack[0].m_obj;
lean_object* v___y_624_ = stack[1].m_obj;
lean_object* v___y_625_ = stack[2].m_obj;
lean_object* v___y_626_ = stack[3].m_obj;
lean_object* v___y_627_ = stack[4].m_obj;
lean_object* v___y_628_ = stack[5].m_obj;
lean_object* v___y_629_ = stack[6].m_obj;
lean_object* v___y_630_ = stack[7].m_obj;
lean_object* v___y_631_ = stack[8].m_obj;
lean_object* v___y_632_ = stack[9].m_obj;
lean_object* v_res_700_;
v_res_700_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(v_e_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed(lean_object* v_e_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(v_e_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
return v_res_712_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___f_724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_724_, 0, v_e_713_);
v___x_725_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_721_);
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_727_ = lean_box(0);
v___x_728_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_726_, v___x_725_, v___f_724_, v___x_727_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec_ref(v___x_725_);
return v___x_728_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_713_ = stack[0].m_obj;
lean_object* v_a_714_ = stack[1].m_obj;
lean_object* v_a_715_ = stack[2].m_obj;
lean_object* v_a_716_ = stack[3].m_obj;
lean_object* v_a_717_ = stack[4].m_obj;
lean_object* v_a_718_ = stack[5].m_obj;
lean_object* v_a_719_ = stack[6].m_obj;
lean_object* v_a_720_ = stack[7].m_obj;
lean_object* v_a_721_ = stack[8].m_obj;
lean_object* v_a_722_ = stack[9].m_obj;
lean_object* v_res_729_;
v_res_729_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___boxed(lean_object* v_e_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
return v_res_741_;
}
}
lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; lean_object* v_a_754_; uint8_t v___x_755_; 
v___x_753_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_750_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref(v___x_753_);
v___x_755_ = lean_unbox(v_a_754_);
lean_dec(v_a_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
return v___x_757_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_simpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_742_ = stack[0].m_obj;
lean_object* v_a_743_ = stack[1].m_obj;
lean_object* v_a_744_ = stack[2].m_obj;
lean_object* v_a_745_ = stack[3].m_obj;
lean_object* v_a_746_ = stack[4].m_obj;
lean_object* v_a_747_ = stack[5].m_obj;
lean_object* v_a_748_ = stack[6].m_obj;
lean_object* v_a_749_ = stack[7].m_obj;
lean_object* v_a_750_ = stack[8].m_obj;
lean_object* v_a_751_ = stack[9].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Meta_Grind_simpCore(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Grind_simpCore(v_e_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
return v_res_770_;
}
}
lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_a_783_; uint8_t v___x_784_; 
v___x_782_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_779_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = lean_unbox(v_a_783_);
lean_dec(v_a_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_786_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_dsimpCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_771_ = stack[0].m_obj;
lean_object* v_a_772_ = stack[1].m_obj;
lean_object* v_a_773_ = stack[2].m_obj;
lean_object* v_a_774_ = stack[3].m_obj;
lean_object* v_a_775_ = stack[4].m_obj;
lean_object* v_a_776_ = stack[5].m_obj;
lean_object* v_a_777_ = stack[6].m_obj;
lean_object* v_a_778_ = stack[7].m_obj;
lean_object* v_a_779_ = stack[8].m_obj;
lean_object* v_a_780_ = stack[9].m_obj;
lean_object* v_res_787_;
v_res_787_ = l_Lean_Meta_Grind_dsimpCore(v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
stack->m_obj
 = v_res_787_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_Grind_dsimpCore(v_e_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
return v_res_799_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = l_Lean_Expr_hasMVar(v_e_800_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_e_800_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v_mctx_806_; lean_object* v___x_807_; lean_object* v_fst_808_; lean_object* v_snd_809_; lean_object* v___x_810_; lean_object* v_cache_811_; lean_object* v_zetaDeltaFVarIds_812_; lean_object* v_postponed_813_; lean_object* v_diag_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_823_; 
v___x_805_ = lean_st_ref_get(v___y_801_);
v_mctx_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_mctx_806_);
lean_dec(v___x_805_);
v___x_807_ = l_Lean_instantiateMVarsCore(v_mctx_806_, v_e_800_);
v_fst_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_fst_808_);
v_snd_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_snd_809_);
lean_dec_ref(v___x_807_);
v___x_810_ = lean_st_ref_take(v___y_801_);
v_cache_811_ = lean_ctor_get(v___x_810_, 1);
v_zetaDeltaFVarIds_812_ = lean_ctor_get(v___x_810_, 2);
v_postponed_813_ = lean_ctor_get(v___x_810_, 3);
v_diag_814_ = lean_ctor_get(v___x_810_, 4);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_810_, 0);
lean_dec(v_unused_824_);
v___x_816_ = v___x_810_;
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_diag_814_);
lean_inc(v_postponed_813_);
lean_inc(v_zetaDeltaFVarIds_812_);
lean_inc(v_cache_811_);
lean_dec(v___x_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_snd_809_);
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_snd_809_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_cache_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_zetaDeltaFVarIds_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_postponed_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_diag_814_);
v___x_819_ = v_reuseFailAlloc_822_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_st_ref_put(v___y_801_, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_fst_808_);
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_800_ = stack[0].m_obj;
lean_object* v___y_801_ = stack[1].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_800_, v___y_801_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_826_, v___y_827_);
lean_dec(v___y_827_);
return v_res_829_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_830_, v___y_838_);
return v___x_842_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_830_ = stack[0].m_obj;
lean_object* v___y_831_ = stack[1].m_obj;
lean_object* v___y_832_ = stack[2].m_obj;
lean_object* v___y_833_ = stack[3].m_obj;
lean_object* v___y_834_ = stack[4].m_obj;
lean_object* v___y_835_ = stack[5].m_obj;
lean_object* v___y_836_ = stack[6].m_obj;
lean_object* v___y_837_ = stack[7].m_obj;
lean_object* v___y_838_ = stack[8].m_obj;
lean_object* v___y_839_ = stack[9].m_obj;
lean_object* v___y_840_ = stack[10].m_obj;
lean_object* v_res_843_;
v_res_843_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
return v_res_856_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_env_864_; uint8_t v___x_865_; lean_object* v_env_866_; lean_object* v___x_867_; lean_object* v_toCold_868_; lean_object* v_mctx_869_; lean_object* v_lctx_870_; lean_object* v_options_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_863_ = lean_st_ref_get(v___y_861_);
v_env_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_env_864_);
lean_dec(v___x_863_);
v___x_865_ = 0;
v_env_866_ = l_Lean_Environment_setRecordingDeps(v_env_864_, v___x_865_);
v___x_867_ = lean_st_ref_get(v___y_859_);
v_toCold_868_ = lean_ctor_get(v___y_860_, 0);
v_mctx_869_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_mctx_869_);
lean_dec(v___x_867_);
v_lctx_870_ = lean_ctor_get(v___y_858_, 2);
v_options_871_ = lean_ctor_get(v_toCold_868_, 2);
lean_inc_ref(v_options_871_);
lean_inc_ref(v_lctx_870_);
v___x_872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_872_, 0, v_env_866_);
lean_ctor_set(v___x_872_, 1, v_mctx_869_);
lean_ctor_set(v___x_872_, 2, v_lctx_870_);
lean_ctor_set(v___x_872_, 3, v_options_871_);
v___x_873_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_msgData_857_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_857_ = stack[0].m_obj;
lean_object* v___y_858_ = stack[1].m_obj;
lean_object* v___y_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v_res_875_;
v_res_875_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_883_; double v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_float_of_nat(v___x_883_);
return v___x_884_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_ref_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_942_; 
v_ref_895_ = lean_ctor_get(v___y_892_, 2);
v___x_896_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_942_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_942_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_942_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v_traceState_902_; lean_object* v_env_903_; lean_object* v_nextMacroScope_904_; lean_object* v_ngen_905_; lean_object* v_auxDeclNGen_906_; lean_object* v_cache_907_; lean_object* v_recordedDeps_908_; lean_object* v_messages_909_; lean_object* v_infoState_910_; lean_object* v_snapshotTasks_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_941_; 
v___x_901_ = lean_st_ref_take(v___y_893_);
v_traceState_902_ = lean_ctor_get(v___x_901_, 4);
v_env_903_ = lean_ctor_get(v___x_901_, 0);
v_nextMacroScope_904_ = lean_ctor_get(v___x_901_, 1);
v_ngen_905_ = lean_ctor_get(v___x_901_, 2);
v_auxDeclNGen_906_ = lean_ctor_get(v___x_901_, 3);
v_cache_907_ = lean_ctor_get(v___x_901_, 5);
v_recordedDeps_908_ = lean_ctor_get(v___x_901_, 6);
v_messages_909_ = lean_ctor_get(v___x_901_, 7);
v_infoState_910_ = lean_ctor_get(v___x_901_, 8);
v_snapshotTasks_911_ = lean_ctor_get(v___x_901_, 9);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_941_ == 0)
{
v___x_913_ = v___x_901_;
v_isShared_914_ = v_isSharedCheck_941_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snapshotTasks_911_);
lean_inc(v_infoState_910_);
lean_inc(v_messages_909_);
lean_inc(v_recordedDeps_908_);
lean_inc(v_cache_907_);
lean_inc(v_traceState_902_);
lean_inc(v_auxDeclNGen_906_);
lean_inc(v_ngen_905_);
lean_inc(v_nextMacroScope_904_);
lean_inc(v_env_903_);
lean_dec(v___x_901_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_941_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint64_t v_tid_915_; lean_object* v_traces_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_940_; 
v_tid_915_ = lean_ctor_get_uint64(v_traceState_902_, sizeof(void*)*1);
v_traces_916_ = lean_ctor_get(v_traceState_902_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_traceState_902_);
if (v_isSharedCheck_940_ == 0)
{
v___x_918_ = v_traceState_902_;
v_isShared_919_ = v_isSharedCheck_940_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_traces_916_);
lean_dec(v_traceState_902_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_940_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; double v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_920_ = lean_box(0);
v___x_921_ = lean_box(0);
v___x_922_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_923_ = 0;
v___x_924_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_925_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_925_, 0, v_cls_888_);
lean_ctor_set(v___x_925_, 1, v___x_921_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set_float(v___x_925_, sizeof(void*)*3, v___x_922_);
lean_ctor_set_float(v___x_925_, sizeof(void*)*3 + 8, v___x_922_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*3 + 16, v___x_923_);
v___x_926_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_927_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v_a_897_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_inc(v_ref_895_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_ref_895_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_PersistentArray_push___redArg(v_traces_916_, v___x_928_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_929_);
v___x_931_ = v___x_918_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_929_);
lean_ctor_set_uint64(v_reuseFailAlloc_939_, sizeof(void*)*1, v_tid_915_);
v___x_931_ = v_reuseFailAlloc_939_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 4, v___x_931_);
v___x_933_ = v___x_913_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_env_903_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_nextMacroScope_904_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_ngen_905_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_auxDeclNGen_906_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 5, v_cache_907_);
lean_ctor_set(v_reuseFailAlloc_938_, 6, v_recordedDeps_908_);
lean_ctor_set(v_reuseFailAlloc_938_, 7, v_messages_909_);
lean_ctor_set(v_reuseFailAlloc_938_, 8, v_infoState_910_);
lean_ctor_set(v_reuseFailAlloc_938_, 9, v_snapshotTasks_911_);
v___x_933_ = v_reuseFailAlloc_938_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_st_ref_put(v___y_893_, v___x_933_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_920_);
v___x_936_ = v___x_899_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_920_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_888_ = stack[0].m_obj;
lean_object* v_msg_889_ = stack[1].m_obj;
lean_object* v___y_890_ = stack[2].m_obj;
lean_object* v___y_891_ = stack[3].m_obj;
lean_object* v___y_892_ = stack[4].m_obj;
lean_object* v___y_893_ = stack[5].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_888_, v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_944_, lean_object* v_msg_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_944_, v_msg_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_962_ = l_Lean_Name_append(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
lean_object* lean_grind_preprocess(lean_object* v_e_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_a_979_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_966_, v_a_974_);
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_n(v_a_979_, 2);
lean_dec_ref(v___x_978_);
v___x_980_ = l_Lean_Meta_Grind_simpCore(v_a_979_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_expr_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_985_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v_expr_982_ = lean_ctor_get(v_a_981_, 0);
lean_inc_ref(v_expr_982_);
v___x_983_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_982_, v_a_974_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lean_Meta_Sym_unfoldReducible(v_a_984_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_986_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_988_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_990_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_Meta_Grind_foldProjs(v_a_992_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = l_Lean_Meta_Sym_normalizeLevels(v_a_994_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_996_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc_n(v_a_998_, 2);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_981_, v_a_998_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_expr_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v_expr_1001_ = lean_ctor_get(v_a_998_, 0);
lean_inc_ref(v_expr_1001_);
lean_dec(v_a_998_);
v___x_1002_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_1001_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_n(v_a_1003_, 2);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_1000_, v_a_1003_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v_expr_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v_expr_1006_ = lean_ctor_get(v_a_1003_, 0);
lean_inc_ref(v_expr_1006_);
lean_dec(v_a_1003_);
v___x_1007_ = l_Lean_Meta_Sym_canon(v_expr_1006_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_Meta_Sym_shareCommon(v_a_1008_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1058_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1058_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1058_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_toCold_1028_; lean_object* v_options_1029_; uint8_t v_hasTrace_1030_; 
v_toCold_1028_ = lean_ctor_get(v_a_975_, 0);
v_options_1029_ = lean_ctor_get(v_toCold_1028_, 2);
v_hasTrace_1030_ = lean_ctor_get_uint8(v_options_1029_, sizeof(void*)*1);
if (v_hasTrace_1030_ == 0)
{
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
goto v___jp_1014_;
}
else
{
lean_object* v_inheritedTraceOptions_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_inheritedTraceOptions_1031_ = lean_ctor_get(v_toCold_1028_, 11);
v___x_1032_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_1034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1031_, v_options_1029_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
goto v___jp_1014_;
}
else
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Grind_updateLastTag(v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref_known(v___x_1035_, 1);
v___x_1036_ = l_Lean_MessageData_ofExpr(v_a_979_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
lean_inc(v_a_1010_);
v___x_1039_ = l_Lean_MessageData_ofExpr(v_a_1010_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1032_, v___x_1040_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_dec_ref_known(v___x_1041_, 1);
goto v___jp_1014_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_1012_);
lean_dec(v_a_1010_);
lean_dec(v_a_1005_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_del_object(v___x_1012_);
lean_dec(v_a_1010_);
lean_dec(v_a_1005_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
v_a_1050_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1035_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1035_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
v___jp_1014_:
{
lean_object* v_proof_x3f_1015_; uint8_t v_cache_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1026_; 
v_proof_x3f_1015_ = lean_ctor_get(v_a_1005_, 1);
v_cache_1016_ = lean_ctor_get_uint8(v_a_1005_, sizeof(void*)*2);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_a_1005_, 0);
lean_dec(v_unused_1027_);
v___x_1018_ = v_a_1005_;
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_proof_x3f_1015_);
lean_dec(v_a_1005_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v_a_1010_);
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1010_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_proof_x3f_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*2, v_cache_1016_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1021_);
v___x_1023_ = v___x_1012_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_a_1005_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1059_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1009_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1009_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1005_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1067_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1007_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1007_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_dec(v_a_1003_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v___x_1004_;
}
}
else
{
lean_dec(v_a_1000_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v___x_1002_;
}
}
else
{
lean_dec(v_a_998_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v___x_999_;
}
}
else
{
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v___x_997_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1075_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_995_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_995_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1083_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_993_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_993_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1091_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_991_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_991_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1099_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_989_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_989_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1107_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_987_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_987_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
v_a_1115_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_985_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_985_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
return v___x_980_;
}
}
}
LEAN_EXPORT void lean_grind_preprocess_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_966_ = stack[0].m_obj;
lean_object* v_a_967_ = stack[1].m_obj;
lean_object* v_a_968_ = stack[2].m_obj;
lean_object* v_a_969_ = stack[3].m_obj;
lean_object* v_a_970_ = stack[4].m_obj;
lean_object* v_a_971_ = stack[5].m_obj;
lean_object* v_a_972_ = stack[6].m_obj;
lean_object* v_a_973_ = stack[7].m_obj;
lean_object* v_a_974_ = stack[8].m_obj;
lean_object* v_a_975_ = stack[9].m_obj;
lean_object* v_a_976_ = stack[10].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = lean_grind_preprocess(v_e_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = lean_grind_preprocess(v_e_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v_res_1136_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_1137_, lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_1137_, v_msg_1138_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1137_ = stack[0].m_obj;
lean_object* v_msg_1138_ = stack[1].m_obj;
lean_object* v___y_1139_ = stack[2].m_obj;
lean_object* v___y_1140_ = stack[3].m_obj;
lean_object* v___y_1141_ = stack[4].m_obj;
lean_object* v___y_1142_ = stack[5].m_obj;
lean_object* v___y_1143_ = stack[6].m_obj;
lean_object* v___y_1144_ = stack[7].m_obj;
lean_object* v___y_1145_ = stack[8].m_obj;
lean_object* v___y_1146_ = stack[9].m_obj;
lean_object* v___y_1147_ = stack[10].m_obj;
lean_object* v___y_1148_ = stack[11].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_1137_, v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_1152_, v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec(v___y_1154_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_1174_ = l_Lean_Name_append(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_1187_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_1188_ = l_Lean_mkConst(v___x_1187_, v___x_1186_);
return v___x_1188_;
}
}
lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_1189_, lean_object* v_proof_1190_, lean_object* v_generation_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; 
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_prop_1189_);
v___x_1203_ = lean_grind_preprocess(v_prop_1189_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1273_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1273_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1273_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_expr_1208_; lean_object* v_proof_x3f_1209_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1256_; 
v_expr_1208_ = lean_ctor_get(v_a_1204_, 0);
lean_inc_ref(v_expr_1208_);
v_proof_x3f_1209_ = lean_ctor_get(v_a_1204_, 1);
lean_inc(v_proof_x3f_1209_);
lean_dec(v_a_1204_);
if (lean_obj_tag(v_proof_x3f_1209_) == 1)
{
lean_object* v_val_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_val_1270_ = lean_ctor_get(v_proof_x3f_1209_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_proof_x3f_1209_, 1);
v___x_1271_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_1208_);
lean_inc_ref(v_prop_1189_);
v___x_1272_ = l_Lean_mkApp4(v___x_1271_, v_prop_1189_, v_expr_1208_, v_val_1270_, v_proof_1190_);
v___y_1256_ = v___x_1272_;
goto v___jp_1255_;
}
else
{
lean_dec(v_proof_x3f_1209_);
v___y_1256_ = v_proof_1190_;
goto v___jp_1255_;
}
v___jp_1210_:
{
lean_object* v___x_1213_; lean_object* v_toGoalState_1214_; lean_object* v_mvarId_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1254_; 
v___x_1213_ = lean_st_ref_take(v___y_1212_);
v_toGoalState_1214_ = lean_ctor_get(v___x_1213_, 0);
v_mvarId_1215_ = lean_ctor_get(v___x_1213_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1217_ = v___x_1213_;
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_mvarId_1215_);
lean_inc(v_toGoalState_1214_);
lean_dec(v___x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_nextDeclIdx_1219_; lean_object* v_enodeMap_1220_; lean_object* v_exprs_1221_; lean_object* v_parents_1222_; lean_object* v_congrTable_1223_; lean_object* v_appMap_1224_; lean_object* v_indicesFound_1225_; lean_object* v_toProcess_1226_; uint8_t v_inconsistent_1227_; lean_object* v_nextIdx_1228_; lean_object* v_newRawFacts_1229_; lean_object* v_facts_1230_; lean_object* v_extThms_1231_; lean_object* v_ematch_1232_; lean_object* v_inj_1233_; lean_object* v_split_1234_; lean_object* v_clean_1235_; lean_object* v_sstates_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1253_; 
v_nextDeclIdx_1219_ = lean_ctor_get(v_toGoalState_1214_, 0);
v_enodeMap_1220_ = lean_ctor_get(v_toGoalState_1214_, 1);
v_exprs_1221_ = lean_ctor_get(v_toGoalState_1214_, 2);
v_parents_1222_ = lean_ctor_get(v_toGoalState_1214_, 3);
v_congrTable_1223_ = lean_ctor_get(v_toGoalState_1214_, 4);
v_appMap_1224_ = lean_ctor_get(v_toGoalState_1214_, 5);
v_indicesFound_1225_ = lean_ctor_get(v_toGoalState_1214_, 6);
v_toProcess_1226_ = lean_ctor_get(v_toGoalState_1214_, 7);
v_inconsistent_1227_ = lean_ctor_get_uint8(v_toGoalState_1214_, sizeof(void*)*17);
v_nextIdx_1228_ = lean_ctor_get(v_toGoalState_1214_, 8);
v_newRawFacts_1229_ = lean_ctor_get(v_toGoalState_1214_, 9);
v_facts_1230_ = lean_ctor_get(v_toGoalState_1214_, 10);
v_extThms_1231_ = lean_ctor_get(v_toGoalState_1214_, 11);
v_ematch_1232_ = lean_ctor_get(v_toGoalState_1214_, 12);
v_inj_1233_ = lean_ctor_get(v_toGoalState_1214_, 13);
v_split_1234_ = lean_ctor_get(v_toGoalState_1214_, 14);
v_clean_1235_ = lean_ctor_get(v_toGoalState_1214_, 15);
v_sstates_1236_ = lean_ctor_get(v_toGoalState_1214_, 16);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_toGoalState_1214_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1238_ = v_toGoalState_1214_;
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_sstates_1236_);
lean_inc(v_clean_1235_);
lean_inc(v_split_1234_);
lean_inc(v_inj_1233_);
lean_inc(v_ematch_1232_);
lean_inc(v_extThms_1231_);
lean_inc(v_facts_1230_);
lean_inc(v_newRawFacts_1229_);
lean_inc(v_nextIdx_1228_);
lean_inc(v_toProcess_1226_);
lean_inc(v_indicesFound_1225_);
lean_inc(v_appMap_1224_);
lean_inc(v_congrTable_1223_);
lean_inc(v_parents_1222_);
lean_inc(v_exprs_1221_);
lean_inc(v_enodeMap_1220_);
lean_inc(v_nextDeclIdx_1219_);
lean_dec(v_toGoalState_1214_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1241_, 0, v_expr_1208_);
lean_ctor_set(v___x_1241_, 1, v___y_1211_);
lean_ctor_set(v___x_1241_, 2, v_generation_1191_);
v___x_1242_ = lean_array_push(v_toProcess_1226_, v___x_1241_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 7, v___x_1242_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_nextDeclIdx_1219_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_enodeMap_1220_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_exprs_1221_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_parents_1222_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_congrTable_1223_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_appMap_1224_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_indicesFound_1225_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_nextIdx_1228_);
lean_ctor_set(v_reuseFailAlloc_1252_, 9, v_newRawFacts_1229_);
lean_ctor_set(v_reuseFailAlloc_1252_, 10, v_facts_1230_);
lean_ctor_set(v_reuseFailAlloc_1252_, 11, v_extThms_1231_);
lean_ctor_set(v_reuseFailAlloc_1252_, 12, v_ematch_1232_);
lean_ctor_set(v_reuseFailAlloc_1252_, 13, v_inj_1233_);
lean_ctor_set(v_reuseFailAlloc_1252_, 14, v_split_1234_);
lean_ctor_set(v_reuseFailAlloc_1252_, 15, v_clean_1235_);
lean_ctor_set(v_reuseFailAlloc_1252_, 16, v_sstates_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*17, v_inconsistent_1227_);
v___x_1244_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1244_);
v___x_1246_ = v___x_1217_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_mvarId_1215_);
v___x_1246_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_st_ref_put(v___y_1212_, v___x_1246_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1240_);
v___x_1249_ = v___x_1206_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1240_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
v___jp_1255_:
{
lean_object* v_toCold_1257_; lean_object* v_options_1258_; uint8_t v_hasTrace_1259_; 
v_toCold_1257_ = lean_ctor_get(v_a_1200_, 0);
v_options_1258_ = lean_ctor_get(v_toCold_1257_, 2);
v_hasTrace_1259_ = lean_ctor_get_uint8(v_options_1258_, sizeof(void*)*1);
if (v_hasTrace_1259_ == 0)
{
lean_dec_ref(v_prop_1189_);
v___y_1211_ = v___y_1256_;
v___y_1212_ = v_a_1192_;
goto v___jp_1210_;
}
else
{
lean_object* v_inheritedTraceOptions_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_inheritedTraceOptions_1260_ = lean_ctor_get(v_toCold_1257_, 11);
v___x_1261_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1262_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1263_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1260_, v_options_1258_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_prop_1189_);
v___y_1211_ = v___y_1256_;
v___y_1212_ = v_a_1192_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1264_ = l_Lean_MessageData_ofExpr(v_prop_1189_);
v___x_1265_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_inc_ref(v_expr_1208_);
v___x_1267_ = l_Lean_MessageData_ofExpr(v_expr_1208_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1261_, v___x_1268_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_dec_ref_known(v___x_1269_, 1);
v___y_1211_ = v___y_1256_;
v___y_1212_ = v_a_1192_;
goto v___jp_1210_;
}
else
{
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_expr_1208_);
lean_del_object(v___x_1206_);
lean_dec(v_generation_1191_);
return v___x_1269_;
}
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_generation_1191_);
lean_dec_ref(v_proof_1190_);
lean_dec_ref(v_prop_1189_);
v_a_1274_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1203_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1203_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_pushNewFact_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_prop_1189_ = stack[0].m_obj;
lean_object* v_proof_1190_ = stack[1].m_obj;
lean_object* v_generation_1191_ = stack[2].m_obj;
lean_object* v_a_1192_ = stack[3].m_obj;
lean_object* v_a_1193_ = stack[4].m_obj;
lean_object* v_a_1194_ = stack[5].m_obj;
lean_object* v_a_1195_ = stack[6].m_obj;
lean_object* v_a_1196_ = stack[7].m_obj;
lean_object* v_a_1197_ = stack[8].m_obj;
lean_object* v_a_1198_ = stack[9].m_obj;
lean_object* v_a_1199_ = stack[10].m_obj;
lean_object* v_a_1200_ = stack[11].m_obj;
lean_object* v_a_1201_ = stack[12].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_1189_, v_proof_1190_, v_generation_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_1283_, lean_object* v_proof_1284_, lean_object* v_generation_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_1283_, v_proof_1284_, v_generation_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
return v_res_1297_;
}
}
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_1298_, lean_object* v_generation_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_proof_1298_);
v___x_1311_ = lean_infer_type(v_proof_1298_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_toCold_1312_; lean_object* v_options_1313_; uint8_t v_hasTrace_1314_; 
v_toCold_1312_ = lean_ctor_get(v_a_1308_, 0);
v_options_1313_ = lean_ctor_get(v_toCold_1312_, 2);
v_hasTrace_1314_ = lean_ctor_get_uint8(v_options_1313_, sizeof(void*)*1);
if (v_hasTrace_1314_ == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1316_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1315_, v_proof_1298_, v_generation_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1316_;
}
else
{
lean_object* v_a_1317_; lean_object* v_inheritedTraceOptions_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_a_1317_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1311_, 1);
v_inheritedTraceOptions_1318_ = lean_ctor_get(v_toCold_1312_, 11);
v___x_1319_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1320_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1321_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1318_, v_options_1313_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1317_, v_proof_1298_, v_generation_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_inc(v_a_1317_);
v___x_1323_ = l_Lean_MessageData_ofExpr(v_a_1317_);
v___x_1324_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1319_, v___x_1323_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref_known(v___x_1324_, 1);
v___x_1325_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1317_, v_proof_1298_, v_generation_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1325_;
}
else
{
lean_dec(v_a_1317_);
lean_dec(v_generation_1299_);
lean_dec_ref(v_proof_1298_);
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_generation_1299_);
lean_dec_ref(v_proof_1298_);
v_a_1326_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1311_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1311_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_pushNewFact_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_1298_ = stack[0].m_obj;
lean_object* v_generation_1299_ = stack[1].m_obj;
lean_object* v_a_1300_ = stack[2].m_obj;
lean_object* v_a_1301_ = stack[3].m_obj;
lean_object* v_a_1302_ = stack[4].m_obj;
lean_object* v_a_1303_ = stack[5].m_obj;
lean_object* v_a_1304_ = stack[6].m_obj;
lean_object* v_a_1305_ = stack[7].m_obj;
lean_object* v_a_1306_ = stack[8].m_obj;
lean_object* v_a_1307_ = stack[9].m_obj;
lean_object* v_a_1308_ = stack[10].m_obj;
lean_object* v_a_1309_ = stack[11].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l_Lean_Meta_Grind_pushNewFact(v_proof_1298_, v_generation_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_1335_, lean_object* v_generation_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Grind_pushNewFact(v_proof_1335_, v_generation_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec(v_a_1337_);
return v_res_1348_;
}
}
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_a_1361_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_1349_, v_a_1356_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1361_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_1363_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1365_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lean_Meta_Grind_foldProjs(v_a_1367_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1369_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1372_ = l_Lean_Meta_Sym_canon(v_a_1371_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = l_Lean_Meta_Sym_shareCommon(v_a_1373_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1374_;
}
else
{
return v___x_1372_;
}
}
else
{
return v___x_1370_;
}
}
else
{
return v___x_1368_;
}
}
else
{
return v___x_1366_;
}
}
else
{
return v___x_1364_;
}
}
else
{
return v___x_1362_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_preprocessLight___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1349_ = stack[0].m_obj;
lean_object* v_a_1350_ = stack[1].m_obj;
lean_object* v_a_1351_ = stack[2].m_obj;
lean_object* v_a_1352_ = stack[3].m_obj;
lean_object* v_a_1353_ = stack[4].m_obj;
lean_object* v_a_1354_ = stack[5].m_obj;
lean_object* v_a_1355_ = stack[6].m_obj;
lean_object* v_a_1356_ = stack[7].m_obj;
lean_object* v_a_1357_ = stack[8].m_obj;
lean_object* v_a_1358_ = stack[9].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
return v_res_1387_;
}
}
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1388_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_preprocessLight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1388_ = stack[0].m_obj;
lean_object* v_a_1389_ = stack[1].m_obj;
lean_object* v_a_1390_ = stack[2].m_obj;
lean_object* v_a_1391_ = stack[3].m_obj;
lean_object* v_a_1392_ = stack[4].m_obj;
lean_object* v_a_1393_ = stack[5].m_obj;
lean_object* v_a_1394_ = stack[6].m_obj;
lean_object* v_a_1395_ = stack[7].m_obj;
lean_object* v_a_1396_ = stack[8].m_obj;
lean_object* v_a_1397_ = stack[9].m_obj;
lean_object* v_a_1398_ = stack[10].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l_Lean_Meta_Grind_preprocessLight(v_e_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_Grind_preprocessLight(v_e_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec(v_a_1403_);
return v_res_1414_;
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

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
lean_object* v___x_225_; lean_object* v_congrThms_226_; lean_object* v_simp_227_; lean_object* v_symSimp_228_; lean_object* v_symDSimp_229_; lean_object* v_lastTag_230_; lean_object* v_counters_231_; lean_object* v_splitDiags_232_; lean_object* v_ematchDiags_233_; lean_object* v_lawfulEqCmpMap_234_; lean_object* v_reflCmpMap_235_; lean_object* v_anchors_236_; lean_object* v_instanceMap_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_291_; 
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
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_291_ == 0)
{
v___x_239_ = v___x_225_;
v_isShared_240_ = v_isSharedCheck_291_;
goto v_resetjp_238_;
}
else
{
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
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_291_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__2);
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__3);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v___x_242_);
lean_ctor_set(v___x_239_, 2, v___x_241_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_congrThms_226_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_simp_227_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_lastTag_230_);
lean_ctor_set(v_reuseFailAlloc_290_, 5, v_counters_231_);
lean_ctor_set(v_reuseFailAlloc_290_, 6, v_splitDiags_232_);
lean_ctor_set(v_reuseFailAlloc_290_, 7, v_ematchDiags_233_);
lean_ctor_set(v_reuseFailAlloc_290_, 8, v_lawfulEqCmpMap_234_);
lean_ctor_set(v_reuseFailAlloc_290_, 9, v_reflCmpMap_235_);
lean_ctor_set(v_reuseFailAlloc_290_, 10, v_anchors_236_);
lean_ctor_set(v_reuseFailAlloc_290_, 11, v_instanceMap_237_);
v___x_244_ = v_reuseFailAlloc_290_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v_symSimpMethods_246_; lean_object* v_symDSimpMethods_247_; lean_object* v___x_248_; 
v___x_245_ = lean_st_ref_put(v___y_217_, v___x_244_);
v_symSimpMethods_246_ = lean_ctor_get(v___y_216_, 2);
v_symDSimpMethods_247_ = lean_ctor_get(v___y_216_, 3);
lean_inc_ref(v_symDSimpMethods_247_);
lean_inc_ref(v_symSimpMethods_246_);
v___x_248_ = l_Lean_Meta_Grind_symNorm(v_e_214_, v_symSimpMethods_246_, v_symDSimpMethods_247_, v_symSimp_228_, v_symDSimp_229_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_281_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_281_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_281_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_281_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_snd_253_; lean_object* v_fst_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_257_; lean_object* v_congrThms_258_; lean_object* v_simp_259_; lean_object* v_lastTag_260_; lean_object* v_counters_261_; lean_object* v_splitDiags_262_; lean_object* v_ematchDiags_263_; lean_object* v_lawfulEqCmpMap_264_; lean_object* v_reflCmpMap_265_; lean_object* v_anchors_266_; lean_object* v_instanceMap_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
v_snd_253_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_snd_253_);
v_fst_254_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_fst_254_);
lean_dec(v_a_249_);
v_fst_255_ = lean_ctor_get(v_snd_253_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_snd_253_, 1);
lean_inc(v_snd_256_);
lean_dec(v_snd_253_);
v___x_257_ = lean_st_ref_take(v___y_217_);
v_congrThms_258_ = lean_ctor_get(v___x_257_, 0);
v_simp_259_ = lean_ctor_get(v___x_257_, 1);
v_lastTag_260_ = lean_ctor_get(v___x_257_, 4);
v_counters_261_ = lean_ctor_get(v___x_257_, 5);
v_splitDiags_262_ = lean_ctor_get(v___x_257_, 6);
v_ematchDiags_263_ = lean_ctor_get(v___x_257_, 7);
v_lawfulEqCmpMap_264_ = lean_ctor_get(v___x_257_, 8);
v_reflCmpMap_265_ = lean_ctor_get(v___x_257_, 9);
v_anchors_266_ = lean_ctor_get(v___x_257_, 10);
v_instanceMap_267_ = lean_ctor_get(v___x_257_, 11);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_279_ = lean_ctor_get(v___x_257_, 3);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v___x_257_, 2);
lean_dec(v_unused_280_);
v___x_269_ = v___x_257_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_instanceMap_267_);
lean_inc(v_anchors_266_);
lean_inc(v_reflCmpMap_265_);
lean_inc(v_lawfulEqCmpMap_264_);
lean_inc(v_ematchDiags_263_);
lean_inc(v_splitDiags_262_);
lean_inc(v_counters_261_);
lean_inc(v_lastTag_260_);
lean_inc(v_simp_259_);
lean_inc(v_congrThms_258_);
lean_dec(v___x_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 3, v_snd_256_);
lean_ctor_set(v___x_269_, 2, v_fst_255_);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_congrThms_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_simp_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_fst_255_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_snd_256_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_lastTag_260_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_counters_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_splitDiags_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 7, v_ematchDiags_263_);
lean_ctor_set(v_reuseFailAlloc_277_, 8, v_lawfulEqCmpMap_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 9, v_reflCmpMap_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 10, v_anchors_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 11, v_instanceMap_267_);
v___x_272_ = v_reuseFailAlloc_277_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_st_ref_put(v___y_217_, v___x_272_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v_fst_254_);
v___x_275_ = v___x_251_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_fst_254_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_248_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_248_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed(lean_object* v_e_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0(v_e_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___f_316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_316_, 0, v_e_305_);
v___x_317_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_313_);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_318_, v___x_317_, v___f_316_, v___x_319_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec_ref(v___x_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___boxed(lean_object* v_e_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
return v_res_332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__0);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(lean_object* v_e_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_Grind_foldProjs(v_e_338_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = l_Lean_Meta_Sym_preprocessExpr(v_a_350_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v_congrThms_354_; lean_object* v_simp_355_; lean_object* v_symSimp_356_; lean_object* v_symDSimp_357_; lean_object* v_lastTag_358_; lean_object* v_counters_359_; lean_object* v_splitDiags_360_; lean_object* v_ematchDiags_361_; lean_object* v_lawfulEqCmpMap_362_; lean_object* v_reflCmpMap_363_; lean_object* v_anchors_364_; lean_object* v_instanceMap_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_421_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = lean_st_ref_take(v___y_341_);
v_congrThms_354_ = lean_ctor_get(v___x_353_, 0);
v_simp_355_ = lean_ctor_get(v___x_353_, 1);
v_symSimp_356_ = lean_ctor_get(v___x_353_, 2);
v_symDSimp_357_ = lean_ctor_get(v___x_353_, 3);
v_lastTag_358_ = lean_ctor_get(v___x_353_, 4);
v_counters_359_ = lean_ctor_get(v___x_353_, 5);
v_splitDiags_360_ = lean_ctor_get(v___x_353_, 6);
v_ematchDiags_361_ = lean_ctor_get(v___x_353_, 7);
v_lawfulEqCmpMap_362_ = lean_ctor_get(v___x_353_, 8);
v_reflCmpMap_363_ = lean_ctor_get(v___x_353_, 9);
v_anchors_364_ = lean_ctor_get(v___x_353_, 10);
v_instanceMap_365_ = lean_ctor_get(v___x_353_, 11);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_421_ == 0)
{
v___x_367_ = v___x_353_;
v_isShared_368_ = v_isSharedCheck_421_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_instanceMap_365_);
lean_inc(v_anchors_364_);
lean_inc(v_reflCmpMap_363_);
lean_inc(v_lawfulEqCmpMap_362_);
lean_inc(v_ematchDiags_361_);
lean_inc(v_splitDiags_360_);
lean_inc(v_counters_359_);
lean_inc(v_lastTag_358_);
lean_inc(v_symDSimp_357_);
lean_inc(v_symSimp_356_);
lean_inc(v_simp_355_);
lean_inc(v_congrThms_354_);
lean_dec(v___x_353_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_421_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___closed__1);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 3, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_congrThms_354_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_simp_355_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_symSimp_356_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_lastTag_358_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_counters_359_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_splitDiags_360_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_ematchDiags_361_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_lawfulEqCmpMap_362_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_reflCmpMap_363_);
lean_ctor_set(v_reuseFailAlloc_420_, 10, v_anchors_364_);
lean_ctor_set(v_reuseFailAlloc_420_, 11, v_instanceMap_365_);
v___x_371_ = v_reuseFailAlloc_420_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v_symDSimpMethods_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_st_ref_put(v___y_341_, v___x_371_);
v_symDSimpMethods_373_ = lean_ctor_get(v___y_340_, 3);
lean_inc(v_a_352_);
v___x_374_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_374_, 0, v_a_352_);
v___x_375_ = ((lean_object*)(l_Lean_Meta_Grind_symNorm___closed__1));
lean_inc_ref(v_symDSimpMethods_373_);
v___x_376_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_374_, v_symDSimpMethods_373_, v___x_375_, v_symDSimp_357_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_411_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_411_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_411_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_411_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; lean_object* v_congrThms_384_; lean_object* v_simp_385_; lean_object* v_symSimp_386_; lean_object* v_lastTag_387_; lean_object* v_counters_388_; lean_object* v_splitDiags_389_; lean_object* v_ematchDiags_390_; lean_object* v_lawfulEqCmpMap_391_; lean_object* v_reflCmpMap_392_; lean_object* v_anchors_393_; lean_object* v_instanceMap_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_409_; 
v_fst_381_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v_a_377_, 1);
lean_inc(v_snd_382_);
lean_dec(v_a_377_);
v___x_383_ = lean_st_ref_take(v___y_341_);
v_congrThms_384_ = lean_ctor_get(v___x_383_, 0);
v_simp_385_ = lean_ctor_get(v___x_383_, 1);
v_symSimp_386_ = lean_ctor_get(v___x_383_, 2);
v_lastTag_387_ = lean_ctor_get(v___x_383_, 4);
v_counters_388_ = lean_ctor_get(v___x_383_, 5);
v_splitDiags_389_ = lean_ctor_get(v___x_383_, 6);
v_ematchDiags_390_ = lean_ctor_get(v___x_383_, 7);
v_lawfulEqCmpMap_391_ = lean_ctor_get(v___x_383_, 8);
v_reflCmpMap_392_ = lean_ctor_get(v___x_383_, 9);
v_anchors_393_ = lean_ctor_get(v___x_383_, 10);
v_instanceMap_394_ = lean_ctor_get(v___x_383_, 11);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_383_, 3);
lean_dec(v_unused_410_);
v___x_396_ = v___x_383_;
v_isShared_397_ = v_isSharedCheck_409_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_instanceMap_394_);
lean_inc(v_anchors_393_);
lean_inc(v_reflCmpMap_392_);
lean_inc(v_lawfulEqCmpMap_391_);
lean_inc(v_ematchDiags_390_);
lean_inc(v_splitDiags_389_);
lean_inc(v_counters_388_);
lean_inc(v_lastTag_387_);
lean_inc(v_symSimp_386_);
lean_inc(v_simp_385_);
lean_inc(v_congrThms_384_);
lean_dec(v___x_383_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_409_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 3, v_snd_382_);
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_congrThms_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_simp_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_symSimp_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_snd_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_lastTag_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_counters_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_splitDiags_389_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_ematchDiags_390_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_lawfulEqCmpMap_391_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_reflCmpMap_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 10, v_anchors_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 11, v_instanceMap_394_);
v___x_399_ = v_reuseFailAlloc_408_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_st_ref_put(v___y_341_, v___x_399_);
if (lean_obj_tag(v_fst_381_) == 0)
{
lean_object* v___x_402_; 
lean_dec_ref_known(v_fst_381_, 0);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_a_352_);
v___x_402_ = v___x_379_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_352_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v_e_x27_404_; lean_object* v___x_406_; 
lean_dec(v_a_352_);
v_e_x27_404_ = lean_ctor_get(v_fst_381_, 0);
lean_inc_ref(v_e_x27_404_);
lean_dec_ref_known(v_fst_381_, 1);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_e_x27_404_);
v___x_406_ = v___x_379_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_e_x27_404_);
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
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_352_);
v_a_412_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_376_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_376_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
else
{
return v___x_351_;
}
}
else
{
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed(lean_object* v_e_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0(v_e_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___f_446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_446_, 0, v_e_435_);
v___x_447_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_443_);
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_449_ = lean_box(0);
v___x_450_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_448_, v___x_447_, v___f_446_, v___x_449_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec_ref(v___x_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___boxed(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
return v_res_462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_unsigned_to_nat(16u);
v___x_465_ = lean_mk_array(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__0);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___lam__0___closed__0);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_473_ = 1;
v___x_474_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_471_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*2, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(32u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6(void){
_start:
{
size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_unsigned_to_nat(32u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__5);
v___x_486_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_482_);
lean_ctor_set(v___x_486_, 3, v___x_482_);
lean_ctor_set_usize(v___x_486_, 4, v___x_481_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__6);
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__2);
v___x_489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
lean_ctor_set(v___x_489_, 3, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__7);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__4);
v___x_493_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__1);
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__3);
v___x_495_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_493_);
lean_ctor_set(v___x_495_, 3, v___x_492_);
lean_ctor_set(v___x_495_, 4, v___x_491_);
lean_ctor_set(v___x_495_, 5, v___x_490_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(lean_object* v_e_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v_congrThms_508_; lean_object* v_simp_509_; lean_object* v_symSimp_510_; lean_object* v_symDSimp_511_; lean_object* v_lastTag_512_; lean_object* v_counters_513_; lean_object* v_splitDiags_514_; lean_object* v_ematchDiags_515_; lean_object* v_lawfulEqCmpMap_516_; lean_object* v_reflCmpMap_517_; lean_object* v_anchors_518_; lean_object* v_instanceMap_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_570_; 
v___x_507_ = lean_st_ref_take(v___y_499_);
v_congrThms_508_ = lean_ctor_get(v___x_507_, 0);
v_simp_509_ = lean_ctor_get(v___x_507_, 1);
v_symSimp_510_ = lean_ctor_get(v___x_507_, 2);
v_symDSimp_511_ = lean_ctor_get(v___x_507_, 3);
v_lastTag_512_ = lean_ctor_get(v___x_507_, 4);
v_counters_513_ = lean_ctor_get(v___x_507_, 5);
v_splitDiags_514_ = lean_ctor_get(v___x_507_, 6);
v_ematchDiags_515_ = lean_ctor_get(v___x_507_, 7);
v_lawfulEqCmpMap_516_ = lean_ctor_get(v___x_507_, 8);
v_reflCmpMap_517_ = lean_ctor_get(v___x_507_, 9);
v_anchors_518_ = lean_ctor_get(v___x_507_, 10);
v_instanceMap_519_ = lean_ctor_get(v___x_507_, 11);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_570_ == 0)
{
v___x_521_ = v___x_507_;
v_isShared_522_ = v_isSharedCheck_570_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_instanceMap_519_);
lean_inc(v_anchors_518_);
lean_inc(v_reflCmpMap_517_);
lean_inc(v_lawfulEqCmpMap_516_);
lean_inc(v_ematchDiags_515_);
lean_inc(v_splitDiags_514_);
lean_inc(v_counters_513_);
lean_inc(v_lastTag_512_);
lean_inc(v_symDSimp_511_);
lean_inc(v_symSimp_510_);
lean_inc(v_simp_509_);
lean_inc(v_congrThms_508_);
lean_dec(v___x_507_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_570_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_congrThms_508_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_symSimp_510_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_symDSimp_511_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_lastTag_512_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v_counters_513_);
lean_ctor_set(v_reuseFailAlloc_569_, 6, v_splitDiags_514_);
lean_ctor_set(v_reuseFailAlloc_569_, 7, v_ematchDiags_515_);
lean_ctor_set(v_reuseFailAlloc_569_, 8, v_lawfulEqCmpMap_516_);
lean_ctor_set(v_reuseFailAlloc_569_, 9, v_reflCmpMap_517_);
lean_ctor_set(v_reuseFailAlloc_569_, 10, v_anchors_518_);
lean_ctor_set(v_reuseFailAlloc_569_, 11, v_instanceMap_519_);
v___x_525_ = v_reuseFailAlloc_569_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v_simp_527_; lean_object* v_simpMethods_528_; lean_object* v___x_529_; 
v___x_526_ = lean_st_ref_put(v___y_499_, v___x_525_);
v_simp_527_ = lean_ctor_get(v___y_498_, 0);
v_simpMethods_528_ = lean_ctor_get(v___y_498_, 1);
lean_inc_ref(v_simpMethods_528_);
lean_inc_ref(v_simp_527_);
v___x_529_ = l_Lean_Meta_Simp_mainCore(v_e_496_, v_simp_527_, v_simp_509_, v_simpMethods_528_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_560_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_560_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_560_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_560_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_536_; lean_object* v_congrThms_537_; lean_object* v_symSimp_538_; lean_object* v_symDSimp_539_; lean_object* v_lastTag_540_; lean_object* v_counters_541_; lean_object* v_splitDiags_542_; lean_object* v_ematchDiags_543_; lean_object* v_lawfulEqCmpMap_544_; lean_object* v_reflCmpMap_545_; lean_object* v_anchors_546_; lean_object* v_instanceMap_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_558_; 
v_fst_534_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_fst_534_);
v_snd_535_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_snd_535_);
lean_dec(v_a_530_);
v___x_536_ = lean_st_ref_take(v___y_499_);
v_congrThms_537_ = lean_ctor_get(v___x_536_, 0);
v_symSimp_538_ = lean_ctor_get(v___x_536_, 2);
v_symDSimp_539_ = lean_ctor_get(v___x_536_, 3);
v_lastTag_540_ = lean_ctor_get(v___x_536_, 4);
v_counters_541_ = lean_ctor_get(v___x_536_, 5);
v_splitDiags_542_ = lean_ctor_get(v___x_536_, 6);
v_ematchDiags_543_ = lean_ctor_get(v___x_536_, 7);
v_lawfulEqCmpMap_544_ = lean_ctor_get(v___x_536_, 8);
v_reflCmpMap_545_ = lean_ctor_get(v___x_536_, 9);
v_anchors_546_ = lean_ctor_get(v___x_536_, 10);
v_instanceMap_547_ = lean_ctor_get(v___x_536_, 11);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_536_, 1);
lean_dec(v_unused_559_);
v___x_549_ = v___x_536_;
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_instanceMap_547_);
lean_inc(v_anchors_546_);
lean_inc(v_reflCmpMap_545_);
lean_inc(v_lawfulEqCmpMap_544_);
lean_inc(v_ematchDiags_543_);
lean_inc(v_splitDiags_542_);
lean_inc(v_counters_541_);
lean_inc(v_lastTag_540_);
lean_inc(v_symDSimp_539_);
lean_inc(v_symSimp_538_);
lean_inc(v_congrThms_537_);
lean_dec(v___x_536_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v_snd_535_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_congrThms_537_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_symSimp_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_symDSimp_539_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_lastTag_540_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v_counters_541_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_splitDiags_542_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_ematchDiags_543_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_lawfulEqCmpMap_544_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v_reflCmpMap_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 10, v_anchors_546_);
lean_ctor_set(v_reuseFailAlloc_557_, 11, v_instanceMap_547_);
v___x_552_ = v_reuseFailAlloc_557_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_st_ref_put(v___y_499_, v___x_552_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_fst_534_);
v___x_555_ = v___x_532_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_fst_534_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_529_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_529_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed(lean_object* v_e_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0(v_e_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___f_594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_594_, 0, v_e_583_);
v___x_595_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_591_);
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore___closed__0));
v___x_597_ = lean_box(0);
v___x_598_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_596_, v___x_595_, v___f_594_, v___x_597_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v___x_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___boxed(lean_object* v_e_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(lean_object* v_e_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_congrThms_623_; lean_object* v_simp_624_; lean_object* v_symSimp_625_; lean_object* v_symDSimp_626_; lean_object* v_lastTag_627_; lean_object* v_counters_628_; lean_object* v_splitDiags_629_; lean_object* v_ematchDiags_630_; lean_object* v_lawfulEqCmpMap_631_; lean_object* v_reflCmpMap_632_; lean_object* v_anchors_633_; lean_object* v_instanceMap_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_687_; 
v___x_622_ = lean_st_ref_take(v___y_614_);
v_congrThms_623_ = lean_ctor_get(v___x_622_, 0);
v_simp_624_ = lean_ctor_get(v___x_622_, 1);
v_symSimp_625_ = lean_ctor_get(v___x_622_, 2);
v_symDSimp_626_ = lean_ctor_get(v___x_622_, 3);
v_lastTag_627_ = lean_ctor_get(v___x_622_, 4);
v_counters_628_ = lean_ctor_get(v___x_622_, 5);
v_splitDiags_629_ = lean_ctor_get(v___x_622_, 6);
v_ematchDiags_630_ = lean_ctor_get(v___x_622_, 7);
v_lawfulEqCmpMap_631_ = lean_ctor_get(v___x_622_, 8);
v_reflCmpMap_632_ = lean_ctor_get(v___x_622_, 9);
v_anchors_633_ = lean_ctor_get(v___x_622_, 10);
v_instanceMap_634_ = lean_ctor_get(v___x_622_, 11);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_687_ == 0)
{
v___x_636_ = v___x_622_;
v_isShared_637_ = v_isSharedCheck_687_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_instanceMap_634_);
lean_inc(v_anchors_633_);
lean_inc(v_reflCmpMap_632_);
lean_inc(v_lawfulEqCmpMap_631_);
lean_inc(v_ematchDiags_630_);
lean_inc(v_splitDiags_629_);
lean_inc(v_counters_628_);
lean_inc(v_lastTag_627_);
lean_inc(v_symDSimp_626_);
lean_inc(v_symSimp_625_);
lean_inc(v_simp_624_);
lean_inc(v_congrThms_623_);
lean_dec(v___x_622_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_687_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_638_ = lean_unsigned_to_nat(32u);
v___x_639_ = lean_mk_empty_array_with_capacity(v___x_638_);
lean_dec_ref(v___x_639_);
v___x_640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore___lam__0___closed__8);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_640_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_congrThms_623_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_symSimp_625_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_symDSimp_626_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_lastTag_627_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_counters_628_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_splitDiags_629_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v_ematchDiags_630_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_lawfulEqCmpMap_631_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_reflCmpMap_632_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_anchors_633_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_instanceMap_634_);
v___x_642_ = v_reuseFailAlloc_686_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v_simp_644_; lean_object* v_simpMethods_645_; lean_object* v___x_646_; 
v___x_643_ = lean_st_ref_put(v___y_614_, v___x_642_);
v_simp_644_ = lean_ctor_get(v___y_613_, 0);
v_simpMethods_645_ = lean_ctor_get(v___y_613_, 1);
lean_inc_ref(v_simpMethods_645_);
lean_inc_ref(v_simp_644_);
v___x_646_ = l_Lean_Meta_Simp_dsimpMainCore(v_e_611_, v_simp_644_, v_simp_624_, v_simpMethods_645_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_677_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_677_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_677_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_677_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v_congrThms_654_; lean_object* v_symSimp_655_; lean_object* v_symDSimp_656_; lean_object* v_lastTag_657_; lean_object* v_counters_658_; lean_object* v_splitDiags_659_; lean_object* v_ematchDiags_660_; lean_object* v_lawfulEqCmpMap_661_; lean_object* v_reflCmpMap_662_; lean_object* v_anchors_663_; lean_object* v_instanceMap_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_675_; 
v_fst_651_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_fst_651_);
v_snd_652_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_647_);
v___x_653_ = lean_st_ref_take(v___y_614_);
v_congrThms_654_ = lean_ctor_get(v___x_653_, 0);
v_symSimp_655_ = lean_ctor_get(v___x_653_, 2);
v_symDSimp_656_ = lean_ctor_get(v___x_653_, 3);
v_lastTag_657_ = lean_ctor_get(v___x_653_, 4);
v_counters_658_ = lean_ctor_get(v___x_653_, 5);
v_splitDiags_659_ = lean_ctor_get(v___x_653_, 6);
v_ematchDiags_660_ = lean_ctor_get(v___x_653_, 7);
v_lawfulEqCmpMap_661_ = lean_ctor_get(v___x_653_, 8);
v_reflCmpMap_662_ = lean_ctor_get(v___x_653_, 9);
v_anchors_663_ = lean_ctor_get(v___x_653_, 10);
v_instanceMap_664_ = lean_ctor_get(v___x_653_, 11);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_653_, 1);
lean_dec(v_unused_676_);
v___x_666_ = v___x_653_;
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_instanceMap_664_);
lean_inc(v_anchors_663_);
lean_inc(v_reflCmpMap_662_);
lean_inc(v_lawfulEqCmpMap_661_);
lean_inc(v_ematchDiags_660_);
lean_inc(v_splitDiags_659_);
lean_inc(v_counters_658_);
lean_inc(v_lastTag_657_);
lean_inc(v_symDSimp_656_);
lean_inc(v_symSimp_655_);
lean_inc(v_congrThms_654_);
lean_dec(v___x_653_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_snd_652_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_congrThms_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_snd_652_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_symSimp_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_symDSimp_656_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_lastTag_657_);
lean_ctor_set(v_reuseFailAlloc_674_, 5, v_counters_658_);
lean_ctor_set(v_reuseFailAlloc_674_, 6, v_splitDiags_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 7, v_ematchDiags_660_);
lean_ctor_set(v_reuseFailAlloc_674_, 8, v_lawfulEqCmpMap_661_);
lean_ctor_set(v_reuseFailAlloc_674_, 9, v_reflCmpMap_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 10, v_anchors_663_);
lean_ctor_set(v_reuseFailAlloc_674_, 11, v_instanceMap_664_);
v___x_669_ = v_reuseFailAlloc_674_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_st_ref_put(v___y_614_, v___x_669_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_fst_651_);
v___x_672_ = v___x_649_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_fst_651_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_646_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_646_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed(lean_object* v_e_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0(v_e_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(lean_object* v_e_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___f_711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___lam__0___boxed), 11, 1);
lean_closure_set(v___f_711_, 0, v_e_700_);
v___x_712_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_708_);
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore___closed__0));
v___x_714_ = lean_box(0);
v___x_715_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore_spec__0___redArg(v___x_713_, v___x_712_, v___f_711_, v___x_714_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec_ref(v___x_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore___boxed(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; lean_object* v_a_740_; uint8_t v___x_741_; 
v___x_739_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_736_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref(v___x_739_);
v___x_741_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symSimpCore(v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacySimpCore(v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___boxed(lean_object* v_e_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_simpCore(v_e_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* v_e_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_a_768_; uint8_t v___x_769_; 
v___x_767_ = l_Lean_Meta_Grind_isLegacyNormalizer___redArg(v_a_764_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = lean_unbox(v_a_768_);
lean_dec(v_a_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_symDSimpCore(v_e_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_legacyDSimpCore(v_e_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___boxed(lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Grind_dsimpCore(v_e_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(lean_object* v_e_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_Lean_Expr_hasMVar(v_e_784_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_e_784_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v_mctx_790_; lean_object* v___x_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_794_; lean_object* v_cache_795_; lean_object* v_zetaDeltaFVarIds_796_; lean_object* v_postponed_797_; lean_object* v_diag_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v___x_789_ = lean_st_ref_get(v___y_785_);
v_mctx_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_mctx_790_);
lean_dec(v___x_789_);
v___x_791_ = l_Lean_instantiateMVarsCore(v_mctx_790_, v_e_784_);
v_fst_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_fst_792_);
v_snd_793_ = lean_ctor_get(v___x_791_, 1);
lean_inc(v_snd_793_);
lean_dec_ref(v___x_791_);
v___x_794_ = lean_st_ref_take(v___y_785_);
v_cache_795_ = lean_ctor_get(v___x_794_, 1);
v_zetaDeltaFVarIds_796_ = lean_ctor_get(v___x_794_, 2);
v_postponed_797_ = lean_ctor_get(v___x_794_, 3);
v_diag_798_ = lean_ctor_get(v___x_794_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_794_, 0);
lean_dec(v_unused_808_);
v___x_800_ = v___x_794_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_diag_798_);
lean_inc(v_postponed_797_);
lean_inc(v_zetaDeltaFVarIds_796_);
lean_inc(v_cache_795_);
lean_dec(v___x_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_snd_793_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_snd_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_cache_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_zetaDeltaFVarIds_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_postponed_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_diag_798_);
v___x_803_ = v_reuseFailAlloc_806_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_st_ref_put(v___y_785_, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_fst_792_);
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg___boxed(lean_object* v_e_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_809_, v___y_810_);
lean_dec(v___y_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(lean_object* v_e_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_813_, v___y_821_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___boxed(lean_object* v_e_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0(v_e_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___y_827_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(lean_object* v_msgData_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_env_846_; uint8_t v___x_847_; lean_object* v_env_848_; lean_object* v___x_849_; lean_object* v_toCold_850_; lean_object* v_mctx_851_; lean_object* v_lctx_852_; lean_object* v_options_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_845_ = lean_st_ref_get(v___y_843_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v___x_847_ = 0;
v_env_848_ = l_Lean_Environment_setRecordingDeps(v_env_846_, v___x_847_);
v___x_849_ = lean_st_ref_get(v___y_841_);
v_toCold_850_ = lean_ctor_get(v___y_842_, 0);
v_mctx_851_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_mctx_851_);
lean_dec(v___x_849_);
v_lctx_852_ = lean_ctor_get(v___y_840_, 2);
v_options_853_ = lean_ctor_get(v_toCold_850_, 2);
lean_inc_ref(v_options_853_);
lean_inc_ref(v_lctx_852_);
v___x_854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_854_, 0, v_env_848_);
lean_ctor_set(v___x_854_, 1, v_mctx_851_);
lean_ctor_set(v___x_854_, 2, v_lctx_852_);
lean_ctor_set(v___x_854_, 3, v_options_853_);
v___x_855_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_msgData_839_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1___boxed(lean_object* v_msgData_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msgData_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_864_; double v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_float_of_nat(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(lean_object* v_cls_869_, lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_923_; 
v_ref_876_ = lean_ctor_get(v___y_873_, 2);
v___x_877_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1_spec__1(v_msg_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_923_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_923_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_923_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v_traceState_883_; lean_object* v_env_884_; lean_object* v_nextMacroScope_885_; lean_object* v_ngen_886_; lean_object* v_auxDeclNGen_887_; lean_object* v_cache_888_; lean_object* v_recordedDeps_889_; lean_object* v_messages_890_; lean_object* v_infoState_891_; lean_object* v_snapshotTasks_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_922_; 
v___x_882_ = lean_st_ref_take(v___y_874_);
v_traceState_883_ = lean_ctor_get(v___x_882_, 4);
v_env_884_ = lean_ctor_get(v___x_882_, 0);
v_nextMacroScope_885_ = lean_ctor_get(v___x_882_, 1);
v_ngen_886_ = lean_ctor_get(v___x_882_, 2);
v_auxDeclNGen_887_ = lean_ctor_get(v___x_882_, 3);
v_cache_888_ = lean_ctor_get(v___x_882_, 5);
v_recordedDeps_889_ = lean_ctor_get(v___x_882_, 6);
v_messages_890_ = lean_ctor_get(v___x_882_, 7);
v_infoState_891_ = lean_ctor_get(v___x_882_, 8);
v_snapshotTasks_892_ = lean_ctor_get(v___x_882_, 9);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_922_ == 0)
{
v___x_894_ = v___x_882_;
v_isShared_895_ = v_isSharedCheck_922_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snapshotTasks_892_);
lean_inc(v_infoState_891_);
lean_inc(v_messages_890_);
lean_inc(v_recordedDeps_889_);
lean_inc(v_cache_888_);
lean_inc(v_traceState_883_);
lean_inc(v_auxDeclNGen_887_);
lean_inc(v_ngen_886_);
lean_inc(v_nextMacroScope_885_);
lean_inc(v_env_884_);
lean_dec(v___x_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_922_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
uint64_t v_tid_896_; lean_object* v_traces_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_921_; 
v_tid_896_ = lean_ctor_get_uint64(v_traceState_883_, sizeof(void*)*1);
v_traces_897_ = lean_ctor_get(v_traceState_883_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_traceState_883_);
if (v_isSharedCheck_921_ == 0)
{
v___x_899_ = v_traceState_883_;
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_traces_897_);
lean_dec(v_traceState_883_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; double v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_901_ = lean_box(0);
v___x_902_ = lean_box(0);
v___x_903_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__0);
v___x_904_ = 0;
v___x_905_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__1));
v___x_906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_906_, 0, v_cls_869_);
lean_ctor_set(v___x_906_, 1, v___x_902_);
lean_ctor_set(v___x_906_, 2, v___x_905_);
lean_ctor_set_float(v___x_906_, sizeof(void*)*3, v___x_903_);
lean_ctor_set_float(v___x_906_, sizeof(void*)*3 + 8, v___x_903_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*3 + 16, v___x_904_);
v___x_907_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___closed__2));
v___x_908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v_a_878_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
lean_inc(v_ref_876_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_ref_876_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_PersistentArray_push___redArg(v_traces_897_, v___x_909_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_910_);
v___x_912_ = v___x_899_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_910_);
lean_ctor_set_uint64(v_reuseFailAlloc_920_, sizeof(void*)*1, v_tid_896_);
v___x_912_ = v_reuseFailAlloc_920_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v___x_912_);
v___x_914_ = v___x_894_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_env_884_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_nextMacroScope_885_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_ngen_886_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_auxDeclNGen_887_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_cache_888_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_recordedDeps_889_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_messages_890_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_infoState_891_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_snapshotTasks_892_);
v___x_914_ = v_reuseFailAlloc_919_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_st_ref_put(v___y_874_, v___x_914_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_901_);
v___x_917_ = v___x_880_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_901_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg___boxed(lean_object* v_cls_924_, lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_924_, v_msg_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__5(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_942_ = l_Lean_Name_append(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessImpl___closed__7(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__6));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* lean_grind_preprocess(lean_object* v_e_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_960_; 
v___x_958_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_946_, v_a_954_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_n(v_a_959_, 2);
lean_dec_ref(v___x_958_);
v___x_960_ = l_Lean_Meta_Grind_simpCore(v_a_959_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_expr_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_expr_962_ = lean_ctor_get(v_a_961_, 0);
lean_inc_ref(v_expr_962_);
v___x_963_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_expr_962_, v_a_954_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
v___x_965_ = l_Lean_Meta_Sym_unfoldReducible(v_a_964_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_Grind_abstractNestedProofs___redArg(v_a_966_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_968_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_970_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Meta_Grind_foldProjs(v_a_972_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_Meta_Sym_normalizeLevels(v_a_974_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_a_976_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_n(v_a_978_, 2);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_961_, v_a_978_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v_expr_981_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v_expr_981_ = lean_ctor_get(v_a_978_, 0);
lean_inc_ref(v_expr_981_);
lean_dec(v_a_978_);
v___x_982_ = l_Lean_Meta_Grind_replacePreMatchCond(v_expr_981_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_980_, v_a_983_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_expr_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v_expr_986_ = lean_ctor_get(v_a_983_, 0);
lean_inc_ref(v_expr_986_);
lean_dec(v_a_983_);
v___x_987_ = l_Lean_Meta_Sym_canon(v_expr_986_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Meta_Sym_shareCommon(v_a_988_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1038_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1038_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1038_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_toCold_1008_; lean_object* v_options_1009_; uint8_t v_hasTrace_1010_; 
v_toCold_1008_ = lean_ctor_get(v_a_955_, 0);
v_options_1009_ = lean_ctor_get(v_toCold_1008_, 2);
v_hasTrace_1010_ = lean_ctor_get_uint8(v_options_1009_, sizeof(void*)*1);
if (v_hasTrace_1010_ == 0)
{
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
goto v___jp_994_;
}
else
{
lean_object* v_inheritedTraceOptions_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_inheritedTraceOptions_1011_ = lean_ctor_get(v_toCold_1008_, 11);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__2));
v___x_1013_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__5, &l_Lean_Meta_Grind_preprocessImpl___closed__5_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__5);
v___x_1014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1011_, v_options_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
goto v___jp_994_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Meta_Grind_updateLastTag(v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1015_, 1);
v___x_1016_ = l_Lean_MessageData_ofExpr(v_a_959_);
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Grind_preprocessImpl___closed__7, &l_Lean_Meta_Grind_preprocessImpl___closed__7_once, _init_l_Lean_Meta_Grind_preprocessImpl___closed__7);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc(v_a_990_);
v___x_1019_ = l_Lean_MessageData_ofExpr(v_a_990_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1012_, v___x_1020_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_dec_ref_known(v___x_1021_, 1);
goto v___jp_994_;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
lean_dec(v_a_985_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
lean_dec(v_a_985_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
v_a_1030_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1015_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1015_);
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
}
v___jp_994_:
{
lean_object* v_proof_x3f_995_; uint8_t v_cache_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1006_; 
v_proof_x3f_995_ = lean_ctor_get(v_a_985_, 1);
v_cache_996_ = lean_ctor_get_uint8(v_a_985_, sizeof(void*)*2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_a_985_, 0);
lean_dec(v_unused_1007_);
v___x_998_ = v_a_985_;
v_isShared_999_ = v_isSharedCheck_1006_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_proof_x3f_995_);
lean_dec(v_a_985_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1006_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_a_990_);
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_proof_x3f_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*2, v_cache_996_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1001_);
v___x_1003_ = v___x_992_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_985_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1039_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_989_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_989_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_985_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1047_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_987_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_987_);
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
lean_dec(v_a_983_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v___x_984_;
}
}
else
{
lean_dec(v_a_980_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v___x_982_;
}
}
else
{
lean_dec(v_a_978_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v___x_979_;
}
}
else
{
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v___x_977_;
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1055_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_975_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_975_);
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
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1063_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_973_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_973_);
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
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1071_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_971_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_971_);
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
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1079_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_969_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_969_);
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
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1087_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_967_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_967_);
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
lean_dec(v_a_961_);
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
v_a_1095_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_965_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_965_);
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
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessImpl___boxed(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = lean_grind_preprocess(v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(lean_object* v_cls_1116_, lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v_cls_1116_, v_msg_1117_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___boxed(lean_object* v_cls_1130_, lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1(v_cls_1130_, v_msg_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec(v___y_1132_);
return v_res_1143_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1151_ = ((lean_object*)(l_Lean_Meta_Grind_preprocessImpl___closed__4));
v___x_1152_ = l_Lean_Name_append(v___x_1151_, v___x_1150_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__4));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__9));
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__8));
v___x_1166_ = l_Lean_mkConst(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* v_prop_1167_, lean_object* v_proof_1168_, lean_object* v_generation_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; 
lean_inc(v_a_1179_);
lean_inc_ref(v_a_1178_);
lean_inc(v_a_1177_);
lean_inc_ref(v_a_1176_);
lean_inc(v_a_1175_);
lean_inc_ref(v_a_1174_);
lean_inc(v_a_1173_);
lean_inc_ref(v_a_1172_);
lean_inc(v_a_1171_);
lean_inc(v_a_1170_);
lean_inc_ref(v_prop_1167_);
v___x_1181_ = lean_grind_preprocess(v_prop_1167_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1251_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1251_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1251_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_expr_1186_; lean_object* v_proof_x3f_1187_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1234_; 
v_expr_1186_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_expr_1186_);
v_proof_x3f_1187_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_proof_x3f_1187_);
lean_dec(v_a_1182_);
if (lean_obj_tag(v_proof_x3f_1187_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_val_1248_ = lean_ctor_get(v_proof_x3f_1187_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_proof_x3f_1187_, 1);
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__10, &l_Lean_Meta_Grind_pushNewFact_x27___closed__10_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__10);
lean_inc_ref(v_expr_1186_);
lean_inc_ref(v_prop_1167_);
v___x_1250_ = l_Lean_mkApp4(v___x_1249_, v_prop_1167_, v_expr_1186_, v_val_1248_, v_proof_1168_);
v___y_1234_ = v___x_1250_;
goto v___jp_1233_;
}
else
{
lean_dec(v_proof_x3f_1187_);
v___y_1234_ = v_proof_1168_;
goto v___jp_1233_;
}
v___jp_1188_:
{
lean_object* v___x_1191_; lean_object* v_toGoalState_1192_; lean_object* v_mvarId_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1232_; 
v___x_1191_ = lean_st_ref_take(v___y_1190_);
v_toGoalState_1192_ = lean_ctor_get(v___x_1191_, 0);
v_mvarId_1193_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1232_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_mvarId_1193_);
lean_inc(v_toGoalState_1192_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1232_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_nextDeclIdx_1197_; lean_object* v_enodeMap_1198_; lean_object* v_exprs_1199_; lean_object* v_parents_1200_; lean_object* v_congrTable_1201_; lean_object* v_appMap_1202_; lean_object* v_indicesFound_1203_; lean_object* v_newFacts_1204_; uint8_t v_inconsistent_1205_; lean_object* v_nextIdx_1206_; lean_object* v_newRawFacts_1207_; lean_object* v_facts_1208_; lean_object* v_extThms_1209_; lean_object* v_ematch_1210_; lean_object* v_inj_1211_; lean_object* v_split_1212_; lean_object* v_clean_1213_; lean_object* v_sstates_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1231_; 
v_nextDeclIdx_1197_ = lean_ctor_get(v_toGoalState_1192_, 0);
v_enodeMap_1198_ = lean_ctor_get(v_toGoalState_1192_, 1);
v_exprs_1199_ = lean_ctor_get(v_toGoalState_1192_, 2);
v_parents_1200_ = lean_ctor_get(v_toGoalState_1192_, 3);
v_congrTable_1201_ = lean_ctor_get(v_toGoalState_1192_, 4);
v_appMap_1202_ = lean_ctor_get(v_toGoalState_1192_, 5);
v_indicesFound_1203_ = lean_ctor_get(v_toGoalState_1192_, 6);
v_newFacts_1204_ = lean_ctor_get(v_toGoalState_1192_, 7);
v_inconsistent_1205_ = lean_ctor_get_uint8(v_toGoalState_1192_, sizeof(void*)*17);
v_nextIdx_1206_ = lean_ctor_get(v_toGoalState_1192_, 8);
v_newRawFacts_1207_ = lean_ctor_get(v_toGoalState_1192_, 9);
v_facts_1208_ = lean_ctor_get(v_toGoalState_1192_, 10);
v_extThms_1209_ = lean_ctor_get(v_toGoalState_1192_, 11);
v_ematch_1210_ = lean_ctor_get(v_toGoalState_1192_, 12);
v_inj_1211_ = lean_ctor_get(v_toGoalState_1192_, 13);
v_split_1212_ = lean_ctor_get(v_toGoalState_1192_, 14);
v_clean_1213_ = lean_ctor_get(v_toGoalState_1192_, 15);
v_sstates_1214_ = lean_ctor_get(v_toGoalState_1192_, 16);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_toGoalState_1192_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1216_ = v_toGoalState_1192_;
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_sstates_1214_);
lean_inc(v_clean_1213_);
lean_inc(v_split_1212_);
lean_inc(v_inj_1211_);
lean_inc(v_ematch_1210_);
lean_inc(v_extThms_1209_);
lean_inc(v_facts_1208_);
lean_inc(v_newRawFacts_1207_);
lean_inc(v_nextIdx_1206_);
lean_inc(v_newFacts_1204_);
lean_inc(v_indicesFound_1203_);
lean_inc(v_appMap_1202_);
lean_inc(v_congrTable_1201_);
lean_inc(v_parents_1200_);
lean_inc(v_exprs_1199_);
lean_inc(v_enodeMap_1198_);
lean_inc(v_nextDeclIdx_1197_);
lean_dec(v_toGoalState_1192_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1231_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1219_, 0, v_expr_1186_);
lean_ctor_set(v___x_1219_, 1, v___y_1189_);
lean_ctor_set(v___x_1219_, 2, v_generation_1169_);
v___x_1220_ = lean_array_push(v_newFacts_1204_, v___x_1219_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 7, v___x_1220_);
v___x_1222_ = v___x_1216_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_nextDeclIdx_1197_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_enodeMap_1198_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_exprs_1199_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_parents_1200_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_congrTable_1201_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_appMap_1202_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_indicesFound_1203_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_nextIdx_1206_);
lean_ctor_set(v_reuseFailAlloc_1230_, 9, v_newRawFacts_1207_);
lean_ctor_set(v_reuseFailAlloc_1230_, 10, v_facts_1208_);
lean_ctor_set(v_reuseFailAlloc_1230_, 11, v_extThms_1209_);
lean_ctor_set(v_reuseFailAlloc_1230_, 12, v_ematch_1210_);
lean_ctor_set(v_reuseFailAlloc_1230_, 13, v_inj_1211_);
lean_ctor_set(v_reuseFailAlloc_1230_, 14, v_split_1212_);
lean_ctor_set(v_reuseFailAlloc_1230_, 15, v_clean_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 16, v_sstates_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*17, v_inconsistent_1205_);
v___x_1222_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1222_);
v___x_1224_ = v___x_1195_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_mvarId_1193_);
v___x_1224_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_st_ref_put(v___y_1190_, v___x_1224_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1218_);
v___x_1227_ = v___x_1184_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1218_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
v___jp_1233_:
{
lean_object* v_toCold_1235_; lean_object* v_options_1236_; uint8_t v_hasTrace_1237_; 
v_toCold_1235_ = lean_ctor_get(v_a_1178_, 0);
v_options_1236_ = lean_ctor_get(v_toCold_1235_, 2);
v_hasTrace_1237_ = lean_ctor_get_uint8(v_options_1236_, sizeof(void*)*1);
if (v_hasTrace_1237_ == 0)
{
lean_dec_ref(v_prop_1167_);
v___y_1189_ = v___y_1234_;
v___y_1190_ = v_a_1170_;
goto v___jp_1188_;
}
else
{
lean_object* v_inheritedTraceOptions_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_inheritedTraceOptions_1238_ = lean_ctor_get(v_toCold_1235_, 11);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1238_, v_options_1236_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec_ref(v_prop_1167_);
v___y_1189_ = v___y_1234_;
v___y_1190_ = v_a_1170_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1242_ = l_Lean_MessageData_ofExpr(v_prop_1167_);
v___x_1243_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__5, &l_Lean_Meta_Grind_pushNewFact_x27___closed__5_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_inc_ref(v_expr_1186_);
v___x_1245_ = l_Lean_MessageData_ofExpr(v_expr_1186_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1239_, v___x_1246_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_dec_ref_known(v___x_1247_, 1);
v___y_1189_ = v___y_1234_;
v___y_1190_ = v_a_1170_;
goto v___jp_1188_;
}
else
{
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_expr_1186_);
lean_del_object(v___x_1184_);
lean_dec(v_generation_1169_);
return v___x_1247_;
}
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_generation_1169_);
lean_dec_ref(v_proof_1168_);
lean_dec_ref(v_prop_1167_);
v_a_1252_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1181_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1181_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27___boxed(lean_object* v_prop_1260_, lean_object* v_proof_1261_, lean_object* v_generation_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Meta_Grind_pushNewFact_x27(v_prop_1260_, v_proof_1261_, v_generation_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec(v_a_1263_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* v_proof_1275_, lean_object* v_generation_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; 
lean_inc(v_a_1286_);
lean_inc_ref(v_a_1285_);
lean_inc(v_a_1284_);
lean_inc_ref(v_a_1283_);
lean_inc_ref(v_proof_1275_);
v___x_1288_ = lean_infer_type(v_proof_1275_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_toCold_1289_; lean_object* v_options_1290_; uint8_t v_hasTrace_1291_; 
v_toCold_1289_ = lean_ctor_get(v_a_1285_, 0);
v_options_1290_ = lean_ctor_get(v_toCold_1289_, 2);
v_hasTrace_1291_ = lean_ctor_get_uint8(v_options_1290_, sizeof(void*)*1);
if (v_hasTrace_1291_ == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1293_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1292_, v_proof_1275_, v_generation_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1293_;
}
else
{
lean_object* v_a_1294_; lean_object* v_inheritedTraceOptions_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_a_1294_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1288_, 1);
v_inheritedTraceOptions_1295_ = lean_ctor_get(v_toCold_1289_, 11);
v___x_1296_ = ((lean_object*)(l_Lean_Meta_Grind_pushNewFact_x27___closed__2));
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_pushNewFact_x27___closed__3, &l_Lean_Meta_Grind_pushNewFact_x27___closed__3_once, _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
v___x_1298_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1295_, v_options_1290_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1294_, v_proof_1275_, v_generation_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_a_1294_);
v___x_1300_ = l_Lean_MessageData_ofExpr(v_a_1294_);
v___x_1301_ = l_Lean_addTrace___at___00Lean_Meta_Grind_preprocessImpl_spec__1___redArg(v___x_1296_, v___x_1300_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref_known(v___x_1301_, 1);
v___x_1302_ = l_Lean_Meta_Grind_pushNewFact_x27(v_a_1294_, v_proof_1275_, v_generation_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1302_;
}
else
{
lean_dec(v_a_1294_);
lean_dec(v_generation_1276_);
lean_dec_ref(v_proof_1275_);
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_generation_1276_);
lean_dec_ref(v_proof_1275_);
v_a_1303_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1288_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1288_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact___boxed(lean_object* v_proof_1311_, lean_object* v_generation_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Grind_pushNewFact(v_proof_1311_, v_generation_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec(v_a_1313_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object* v_e_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v_a_1337_; lean_object* v___x_1338_; 
v___x_1336_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_preprocessImpl_spec__0___redArg(v_e_1325_, v_a_1332_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1337_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_a_1339_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_1341_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l_Lean_Meta_Grind_foldProjs(v_a_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = l_Lean_Meta_Sym_normalizeLevels(v_a_1345_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = l_Lean_Meta_Sym_canon(v_a_1347_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Meta_Sym_shareCommon(v_a_1349_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1350_;
}
else
{
return v___x_1348_;
}
}
else
{
return v___x_1346_;
}
}
else
{
return v___x_1344_;
}
}
else
{
return v___x_1342_;
}
}
else
{
return v___x_1340_;
}
}
else
{
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___redArg___boxed(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_e_1363_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight___boxed(lean_object* v_e_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_Grind_preprocessLight(v_e_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec(v_a_1377_);
return v_res_1388_;
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

// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Norm
// Imports: import Lean.Elab.Tactic.Grind.Config import Lean.Meta.Tactic.Grind.Main import Lean.Meta.Tactic.Grind.NormSym
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_funBinderTypes;
extern lean_object* l_Lean_pp_match;
extern lean_object* l_Lean_pp_explicit;
lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`grind_norm` discrepancy"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nlegacy:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\nsym:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " (in hidden arguments)"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*17 + 40, .m_other = 17, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 65, 49, 255, 194, 192, 55, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Norm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 227, 116, 195, 231, 106, 69, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 192, 202, 154, 36, 176, 62, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 12, 184, 181, 218, 208, 171, 246)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(59, 178, 245, 218, 212, 66, 68, 138)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__17_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(58, 180, 2, 251, 15, 183, 219, 39)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalGrindNorm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(84, 95, 63, 153, 84, 50, 113, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg(lean_object* v_legacy_22_){
_start:
{
lean_inc(v_legacy_22_);
return v_legacy_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg___boxed(lean_object* v_legacy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg(v_legacy_23_);
lean_dec(v_legacy_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_legacy_28_){
_start:
{
lean_inc(v_legacy_28_);
return v_legacy_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_legacy_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_legacy_32_);
lean_dec(v_legacy_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg(lean_object* v_sym_35_){
_start:
{
lean_inc(v_sym_35_);
return v_sym_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg___boxed(lean_object* v_sym_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg(v_sym_36_);
lean_dec(v_sym_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_sym_41_){
_start:
{
lean_inc(v_sym_41_);
return v_sym_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_sym_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_sym_45_);
lean_dec(v_sym_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg(lean_object* v_check_48_){
_start:
{
lean_inc(v_check_48_);
return v_check_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg___boxed(lean_object* v_check_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg(v_check_49_);
lean_dec(v_check_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_check_54_){
_start:
{
lean_inc(v_check_54_);
return v_check_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_check_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_check_58_);
lean_dec(v_check_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(lean_object* v_e_61_, lean_object* v___y_62_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = l_Lean_Expr_hasMVar(v_e_61_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v_e_61_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v_mctx_67_; lean_object* v___x_68_; lean_object* v_fst_69_; lean_object* v_snd_70_; lean_object* v___x_71_; lean_object* v_cache_72_; lean_object* v_zetaDeltaFVarIds_73_; lean_object* v_postponed_74_; lean_object* v_diag_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_84_; 
v___x_66_ = lean_st_ref_get(v___y_62_);
v_mctx_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_mctx_67_);
lean_dec(v___x_66_);
v___x_68_ = l_Lean_instantiateMVarsCore(v_mctx_67_, v_e_61_);
v_fst_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_fst_69_);
v_snd_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_snd_70_);
lean_dec_ref(v___x_68_);
v___x_71_ = lean_st_ref_take(v___y_62_);
v_cache_72_ = lean_ctor_get(v___x_71_, 1);
v_zetaDeltaFVarIds_73_ = lean_ctor_get(v___x_71_, 2);
v_postponed_74_ = lean_ctor_get(v___x_71_, 3);
v_diag_75_ = lean_ctor_get(v___x_71_, 4);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v___x_71_, 0);
lean_dec(v_unused_85_);
v___x_77_ = v___x_71_;
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_diag_75_);
lean_inc(v_postponed_74_);
lean_inc(v_zetaDeltaFVarIds_73_);
lean_inc(v_cache_72_);
lean_dec(v___x_71_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_snd_70_);
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_snd_70_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_cache_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_zetaDeltaFVarIds_73_);
lean_ctor_set(v_reuseFailAlloc_83_, 3, v_postponed_74_);
lean_ctor_set(v_reuseFailAlloc_83_, 4, v_diag_75_);
v___x_80_ = v_reuseFailAlloc_83_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_st_ref_put(v___y_62_, v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_fst_69_);
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg___boxed(lean_object* v_e_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_e_86_, v___y_87_);
lean_dec(v___y_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(lean_object* v_e_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_e_90_, v___y_96_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___boxed(lean_object* v_e_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(v_e_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(lean_object* v_opts_112_, lean_object* v_opt_113_){
_start:
{
lean_object* v_name_114_; lean_object* v_defValue_115_; lean_object* v_map_116_; lean_object* v___x_117_; 
v_name_114_ = lean_ctor_get(v_opt_113_, 0);
v_defValue_115_ = lean_ctor_get(v_opt_113_, 1);
v_map_116_ = lean_ctor_get(v_opts_112_, 0);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_116_, v_name_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_inc(v_defValue_115_);
return v_defValue_115_;
}
else
{
lean_object* v_val_118_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_117_, 1);
if (lean_obj_tag(v_val_118_) == 3)
{
lean_object* v_v_119_; 
v_v_119_ = lean_ctor_get(v_val_118_, 0);
lean_inc(v_v_119_);
lean_dec_ref_known(v_val_118_, 1);
return v_v_119_;
}
else
{
lean_dec(v_val_118_);
lean_inc(v_defValue_115_);
return v_defValue_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3___boxed(lean_object* v_opts_120_, lean_object* v_opt_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v_opts_120_, v_opt_121_);
lean_dec_ref(v_opt_121_);
lean_dec_ref(v_opts_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(lean_object* v_o_126_, lean_object* v_k_127_, uint8_t v_v_128_){
_start:
{
lean_object* v_map_129_; uint8_t v_hasTrace_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_144_; 
v_map_129_ = lean_ctor_get(v_o_126_, 0);
v_hasTrace_130_ = lean_ctor_get_uint8(v_o_126_, sizeof(void*)*1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_o_126_);
if (v_isSharedCheck_144_ == 0)
{
v___x_132_ = v_o_126_;
v_isShared_133_ = v_isSharedCheck_144_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_map_129_);
lean_dec(v_o_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_144_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_134_, 0, v_v_128_);
lean_inc(v_k_127_);
v___x_135_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_127_, v___x_134_, v_map_129_);
if (v_hasTrace_130_ == 0)
{
lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_139_; 
v___x_136_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__1));
v___x_137_ = l_Lean_Name_isPrefixOf(v___x_136_, v_k_127_);
lean_dec(v_k_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_135_);
v___x_139_ = v___x_132_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_135_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_137_);
return v___x_139_;
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v_k_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_135_);
v___x_142_ = v___x_132_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, sizeof(void*)*1, v_hasTrace_130_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___boxed(lean_object* v_o_145_, lean_object* v_k_146_, lean_object* v_v_147_){
_start:
{
uint8_t v_v_boxed_148_; lean_object* v_res_149_; 
v_v_boxed_148_ = lean_unbox(v_v_147_);
v_res_149_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(v_o_145_, v_k_146_, v_v_boxed_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(lean_object* v_opts_150_, lean_object* v_opt_151_, uint8_t v_val_152_){
_start:
{
lean_object* v_name_153_; lean_object* v___x_154_; 
v_name_153_ = lean_ctor_get(v_opt_151_, 0);
lean_inc(v_name_153_);
lean_dec_ref(v_opt_151_);
v___x_154_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(v_opts_150_, v_name_153_, v_val_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0___boxed(lean_object* v_opts_155_, lean_object* v_opt_156_, lean_object* v_val_157_){
_start:
{
uint8_t v_val_boxed_158_; lean_object* v_res_159_; 
v_val_boxed_158_ = lean_unbox(v_val_157_);
v_res_159_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_opts_155_, v_opt_156_, v_val_boxed_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(uint8_t v___x_160_, uint8_t v___x_161_, lean_object* v_o_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = l_Lean_pp_funBinderTypes;
v___x_164_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_o_162_, v___x_163_, v___x_160_);
v___x_165_ = l_Lean_pp_match;
v___x_166_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v___x_164_, v___x_165_, v___x_161_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0___boxed(lean_object* v___x_167_, lean_object* v___x_168_, lean_object* v_o_169_){
_start:
{
uint8_t v___x_49157__boxed_170_; uint8_t v___x_49158__boxed_171_; lean_object* v_res_172_; 
v___x_49157__boxed_170_ = lean_unbox(v___x_167_);
v___x_49158__boxed_171_ = lean_unbox(v___x_168_);
v_res_172_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(v___x_49157__boxed_170_, v___x_49158__boxed_171_, v_o_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(uint8_t v___x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_pp_explicit;
v___x_176_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_x_174_, v___x_175_, v___x_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1___boxed(lean_object* v___x_177_, lean_object* v_x_178_){
_start:
{
uint8_t v___x_49171__boxed_179_; lean_object* v_res_180_; 
v___x_49171__boxed_179_ = lean_unbox(v___x_177_);
v_res_180_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(v___x_49171__boxed_179_, v_x_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(uint8_t v___x_181_, lean_object* v___f_182_, lean_object* v_o_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = l_Lean_pp_explicit;
v___x_185_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_o_183_, v___x_184_, v___x_181_);
v___x_186_ = lean_apply_1(v___f_182_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2___boxed(lean_object* v___x_187_, lean_object* v___f_188_, lean_object* v_o_189_){
_start:
{
uint8_t v___x_49181__boxed_190_; lean_object* v_res_191_; 
v___x_49181__boxed_190_ = lean_unbox(v___x_187_);
v_res_191_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(v___x_49181__boxed_190_, v___f_188_, v_o_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(lean_object* v_msgData_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; lean_object* v_env_199_; uint8_t v___x_200_; lean_object* v_env_201_; lean_object* v___x_202_; lean_object* v_toCold_203_; lean_object* v_mctx_204_; lean_object* v_lctx_205_; lean_object* v_options_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_198_ = lean_st_ref_get(v___y_196_);
v_env_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_env_199_);
lean_dec(v___x_198_);
v___x_200_ = 0;
v_env_201_ = l_Lean_Environment_setRecordingDeps(v_env_199_, v___x_200_);
v___x_202_ = lean_st_ref_get(v___y_194_);
v_toCold_203_ = lean_ctor_get(v___y_195_, 0);
v_mctx_204_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_mctx_204_);
lean_dec(v___x_202_);
v_lctx_205_ = lean_ctor_get(v___y_193_, 2);
v_options_206_ = lean_ctor_get(v_toCold_203_, 2);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_lctx_205_);
v___x_207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_207_, 0, v_env_201_);
lean_ctor_set(v___x_207_, 1, v_mctx_204_);
lean_ctor_set(v___x_207_, 2, v_lctx_205_);
lean_ctor_set(v___x_207_, 3, v_options_206_);
v___x_208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_msgData_192_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3___boxed(lean_object* v_msgData_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(v_msgData_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(lean_object* v_msg_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_ref_223_; lean_object* v___x_224_; lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_ref_223_ = lean_ctor_get(v___y_220_, 2);
v___x_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(v_msg_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_inc(v_ref_223_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_ref_223_);
lean_ctor_set(v___x_229_, 1, v_a_225_);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg___boxed(lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_240_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__0));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__2));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__4));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(lean_object* v_a_252_, lean_object* v_a_253_, uint8_t v_hidden_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___y_261_; 
if (v_hidden_254_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__6));
v___y_261_ = v___x_274_;
goto v___jp_260_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7));
v___y_261_ = v___x_275_;
goto v___jp_260_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1);
lean_inc_ref(v___y_261_);
v___x_263_ = l_Lean_stringToMessageData(v___y_261_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_indentExpr(v_a_252_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_indentExpr(v_a_253_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_272_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___boxed(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_hidden_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
uint8_t v_hidden_boxed_284_; lean_object* v_res_285_; 
v_hidden_boxed_284_ = lean_unbox(v_hidden_278_);
v_res_285_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_276_, v_a_277_, v_hidden_boxed_284_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_285_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0);
v___x_289_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3);
v___x_292_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_294_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(lean_object* v_a_299_, lean_object* v_a_300_, size_t v___x_301_, size_t v___x_302_, lean_object* v_as_x27_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
if (lean_obj_tag(v_as_x27_303_) == 0)
{
lean_object* v___x_310_; 
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v_b_304_);
return v___x_310_;
}
else
{
lean_object* v_toCold_311_; lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v_currRecDepth_314_; lean_object* v_ref_315_; uint8_t v_suppressElabErrors_316_; uint8_t v_checkDeprecated_317_; uint8_t v_isRecordingDeps_318_; lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_options_321_; lean_object* v_currNamespace_322_; lean_object* v_openDecls_323_; lean_object* v_initHeartbeats_324_; lean_object* v_maxHeartbeats_325_; lean_object* v_quotContext_326_; lean_object* v_currMacroScope_327_; lean_object* v_cancelTk_x3f_328_; lean_object* v_inheritedTraceOptions_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint16_t v___y_333_; lean_object* v___y_334_; lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_currNamespace_337_; lean_object* v_openDecls_338_; lean_object* v_initHeartbeats_339_; lean_object* v_maxHeartbeats_340_; lean_object* v_quotContext_341_; lean_object* v_currMacroScope_342_; lean_object* v_cancelTk_x3f_343_; lean_object* v_inheritedTraceOptions_344_; lean_object* v_currRecDepth_345_; lean_object* v_ref_346_; uint8_t v_suppressElabErrors_347_; uint8_t v_checkDeprecated_348_; uint8_t v_isRecordingDeps_349_; lean_object* v___y_350_; uint16_t v___y_389_; lean_object* v___y_390_; uint8_t v___y_391_; uint16_t v___y_414_; lean_object* v___y_415_; uint8_t v___y_416_; uint8_t v___y_417_; uint8_t v___x_418_; lean_object* v___y_420_; 
v_toCold_311_ = lean_ctor_get(v___y_307_, 0);
v_head_312_ = lean_ctor_get(v_as_x27_303_, 0);
v_tail_313_ = lean_ctor_get(v_as_x27_303_, 1);
v_currRecDepth_314_ = lean_ctor_get(v___y_307_, 1);
v_ref_315_ = lean_ctor_get(v___y_307_, 2);
v_suppressElabErrors_316_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 2);
v_checkDeprecated_317_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 3);
v_isRecordingDeps_318_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 4);
v_fileName_319_ = lean_ctor_get(v_toCold_311_, 0);
v_fileMap_320_ = lean_ctor_get(v_toCold_311_, 1);
v_options_321_ = lean_ctor_get(v_toCold_311_, 2);
v_currNamespace_322_ = lean_ctor_get(v_toCold_311_, 4);
v_openDecls_323_ = lean_ctor_get(v_toCold_311_, 5);
v_initHeartbeats_324_ = lean_ctor_get(v_toCold_311_, 6);
v_maxHeartbeats_325_ = lean_ctor_get(v_toCold_311_, 7);
v_quotContext_326_ = lean_ctor_get(v_toCold_311_, 8);
v_currMacroScope_327_ = lean_ctor_get(v_toCold_311_, 9);
v_cancelTk_x3f_328_ = lean_ctor_get(v_toCold_311_, 10);
v_inheritedTraceOptions_329_ = lean_ctor_get(v_toCold_311_, 11);
v___x_330_ = lean_box(0);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v_isRecordingDeps_318_ == 0)
{
lean_object* v___x_430_; 
lean_inc(v_head_312_);
lean_inc_ref(v_options_321_);
v___x_430_ = lean_apply_1(v_head_312_, v_options_321_);
v___y_420_ = v___x_430_;
goto v___jp_419_;
}
else
{
lean_object* v___x_431_; 
lean_inc_ref(v_options_321_);
v___x_431_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_321_);
v___y_420_ = v___x_431_;
goto v___jp_419_;
}
v___jp_332_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_351_ = l_Lean_maxRecDepth;
v___x_352_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_334_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_353_, 0, v_fileName_335_);
lean_ctor_set(v___x_353_, 1, v_fileMap_336_);
lean_ctor_set(v___x_353_, 2, v___y_334_);
lean_ctor_set(v___x_353_, 3, v___x_352_);
lean_ctor_set(v___x_353_, 4, v_currNamespace_337_);
lean_ctor_set(v___x_353_, 5, v_openDecls_338_);
lean_ctor_set(v___x_353_, 6, v_initHeartbeats_339_);
lean_ctor_set(v___x_353_, 7, v_maxHeartbeats_340_);
lean_ctor_set(v___x_353_, 8, v_quotContext_341_);
lean_ctor_set(v___x_353_, 9, v_currMacroScope_342_);
lean_ctor_set(v___x_353_, 10, v_cancelTk_x3f_343_);
lean_ctor_set(v___x_353_, 11, v_inheritedTraceOptions_344_);
lean_inc(v_ref_346_);
lean_inc(v_currRecDepth_345_);
v___x_354_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_currRecDepth_345_);
lean_ctor_set(v___x_354_, 2, v_ref_346_);
lean_ctor_set_uint16(v___x_354_, sizeof(void*)*3, v___y_333_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3 + 2, v_suppressElabErrors_347_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3 + 3, v_checkDeprecated_348_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3 + 4, v_isRecordingDeps_349_);
lean_inc_ref(v_a_299_);
v___x_355_ = l_Lean_Meta_ppExpr(v_a_299_, v___y_305_, v___y_306_, v___x_354_, v___y_350_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
lean_inc_ref(v_a_300_);
v___x_357_ = l_Lean_Meta_ppExpr(v_a_300_, v___y_305_, v___y_306_, v___x_354_, v___y_350_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = l_Std_Format_defWidth;
v___x_360_ = l_Std_Format_pretty(v_a_356_, v___x_359_, v___x_331_, v___x_331_);
v___x_361_ = l_Std_Format_pretty(v_a_358_, v___x_359_, v___x_331_, v___x_331_);
v___x_362_ = lean_string_dec_eq(v___x_360_, v___x_361_);
lean_dec_ref(v___x_361_);
lean_dec_ref(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_363_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_364_ = l_Lean_indentExpr(v_a_299_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = l_Lean_indentExpr(v_a_300_);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_369_, v___y_305_, v___y_306_, v___x_354_, v___y_350_);
lean_dec_ref_known(v___x_354_, 3);
return v___x_370_;
}
else
{
lean_dec_ref_known(v___x_354_, 3);
v_as_x27_303_ = v_tail_313_;
v_b_304_ = v___x_330_;
goto _start;
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_a_356_);
lean_dec_ref_known(v___x_354_, 3);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
v_a_372_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_357_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_357_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref_known(v___x_354_, 3);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
v_a_380_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_355_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_355_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
v___jp_388_:
{
lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v_nextMacroScope_394_; lean_object* v_ngen_395_; lean_object* v_auxDeclNGen_396_; lean_object* v_traceState_397_; lean_object* v_recordedDeps_398_; lean_object* v_messages_399_; lean_object* v_infoState_400_; lean_object* v_snapshotTasks_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_411_; 
v___x_392_ = lean_st_ref_take(v___y_308_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
v_nextMacroScope_394_ = lean_ctor_get(v___x_392_, 1);
v_ngen_395_ = lean_ctor_get(v___x_392_, 2);
v_auxDeclNGen_396_ = lean_ctor_get(v___x_392_, 3);
v_traceState_397_ = lean_ctor_get(v___x_392_, 4);
v_recordedDeps_398_ = lean_ctor_get(v___x_392_, 6);
v_messages_399_ = lean_ctor_get(v___x_392_, 7);
v_infoState_400_ = lean_ctor_get(v___x_392_, 8);
v_snapshotTasks_401_ = lean_ctor_get(v___x_392_, 9);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_392_, 5);
lean_dec(v_unused_412_);
v___x_403_ = v___x_392_;
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snapshotTasks_401_);
lean_inc(v_infoState_400_);
lean_inc(v_messages_399_);
lean_inc(v_recordedDeps_398_);
lean_inc(v_traceState_397_);
lean_inc(v_auxDeclNGen_396_);
lean_inc(v_ngen_395_);
lean_inc(v_nextMacroScope_394_);
lean_inc(v_env_393_);
lean_dec(v___x_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_Kernel_enableDiag(v_env_393_, v___y_391_);
v___x_406_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 5, v___x_406_);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_nextMacroScope_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_ngen_395_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_auxDeclNGen_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_traceState_397_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_recordedDeps_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_messages_399_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_infoState_400_);
lean_ctor_set(v_reuseFailAlloc_410_, 9, v_snapshotTasks_401_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_st_ref_put(v___y_308_, v___x_408_);
lean_inc_ref(v_inheritedTraceOptions_329_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_currMacroScope_327_);
lean_inc(v_quotContext_326_);
lean_inc(v_maxHeartbeats_325_);
lean_inc(v_initHeartbeats_324_);
lean_inc(v_openDecls_323_);
lean_inc(v_currNamespace_322_);
lean_inc_ref(v_fileMap_320_);
lean_inc_ref(v_fileName_319_);
v___y_333_ = v___y_389_;
v___y_334_ = v___y_390_;
v_fileName_335_ = v_fileName_319_;
v_fileMap_336_ = v_fileMap_320_;
v_currNamespace_337_ = v_currNamespace_322_;
v_openDecls_338_ = v_openDecls_323_;
v_initHeartbeats_339_ = v_initHeartbeats_324_;
v_maxHeartbeats_340_ = v_maxHeartbeats_325_;
v_quotContext_341_ = v_quotContext_326_;
v_currMacroScope_342_ = v_currMacroScope_327_;
v_cancelTk_x3f_343_ = v_cancelTk_x3f_328_;
v_inheritedTraceOptions_344_ = v_inheritedTraceOptions_329_;
v_currRecDepth_345_ = v_currRecDepth_314_;
v_ref_346_ = v_ref_315_;
v_suppressElabErrors_347_ = v_suppressElabErrors_316_;
v_checkDeprecated_348_ = v_checkDeprecated_317_;
v_isRecordingDeps_349_ = v_isRecordingDeps_318_;
v___y_350_ = v___y_308_;
goto v___jp_332_;
}
}
}
v___jp_413_:
{
if (v___y_416_ == 0)
{
v___y_389_ = v___y_414_;
v___y_390_ = v___y_415_;
v___y_391_ = v___y_417_;
goto v___jp_388_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_329_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_currMacroScope_327_);
lean_inc(v_quotContext_326_);
lean_inc(v_maxHeartbeats_325_);
lean_inc(v_initHeartbeats_324_);
lean_inc(v_openDecls_323_);
lean_inc(v_currNamespace_322_);
lean_inc_ref(v_fileMap_320_);
lean_inc_ref(v_fileName_319_);
v___y_333_ = v___y_414_;
v___y_334_ = v___y_415_;
v_fileName_335_ = v_fileName_319_;
v_fileMap_336_ = v_fileMap_320_;
v_currNamespace_337_ = v_currNamespace_322_;
v_openDecls_338_ = v_openDecls_323_;
v_initHeartbeats_339_ = v_initHeartbeats_324_;
v_maxHeartbeats_340_ = v_maxHeartbeats_325_;
v_quotContext_341_ = v_quotContext_326_;
v_currMacroScope_342_ = v_currMacroScope_327_;
v_cancelTk_x3f_343_ = v_cancelTk_x3f_328_;
v_inheritedTraceOptions_344_ = v_inheritedTraceOptions_329_;
v_currRecDepth_345_ = v_currRecDepth_314_;
v_ref_346_ = v_ref_315_;
v_suppressElabErrors_347_ = v_suppressElabErrors_316_;
v_checkDeprecated_348_ = v_checkDeprecated_317_;
v_isRecordingDeps_349_ = v_isRecordingDeps_318_;
v___y_350_ = v___y_308_;
goto v___jp_332_;
}
}
v___jp_419_:
{
uint16_t v___x_421_; lean_object* v___x_422_; lean_object* v_env_423_; uint8_t v___x_424_; uint16_t v___x_425_; uint16_t v___x_426_; uint16_t v___x_427_; uint8_t v___x_428_; 
v___x_421_ = l_Lean_OptionFlags_ofOptions(v___y_420_);
v___x_422_ = lean_st_ref_get(v___y_308_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_423_);
lean_dec_ref(v_env_423_);
v___x_425_ = 512;
v___x_426_ = lean_uint16_land(v___x_421_, v___x_425_);
v___x_427_ = 0;
v___x_428_ = lean_uint16_dec_eq(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 1;
v___y_414_ = v___x_421_;
v___y_415_ = v___y_420_;
v___y_416_ = v___x_424_;
v___y_417_ = v___x_429_;
goto v___jp_413_;
}
else
{
if (v___x_418_ == 0)
{
if (v___x_424_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_329_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_currMacroScope_327_);
lean_inc(v_quotContext_326_);
lean_inc(v_maxHeartbeats_325_);
lean_inc(v_initHeartbeats_324_);
lean_inc(v_openDecls_323_);
lean_inc(v_currNamespace_322_);
lean_inc_ref(v_fileMap_320_);
lean_inc_ref(v_fileName_319_);
v___y_333_ = v___x_421_;
v___y_334_ = v___y_420_;
v_fileName_335_ = v_fileName_319_;
v_fileMap_336_ = v_fileMap_320_;
v_currNamespace_337_ = v_currNamespace_322_;
v_openDecls_338_ = v_openDecls_323_;
v_initHeartbeats_339_ = v_initHeartbeats_324_;
v_maxHeartbeats_340_ = v_maxHeartbeats_325_;
v_quotContext_341_ = v_quotContext_326_;
v_currMacroScope_342_ = v_currMacroScope_327_;
v_cancelTk_x3f_343_ = v_cancelTk_x3f_328_;
v_inheritedTraceOptions_344_ = v_inheritedTraceOptions_329_;
v_currRecDepth_345_ = v_currRecDepth_314_;
v_ref_346_ = v_ref_315_;
v_suppressElabErrors_347_ = v_suppressElabErrors_316_;
v_checkDeprecated_348_ = v_checkDeprecated_317_;
v_isRecordingDeps_349_ = v_isRecordingDeps_318_;
v___y_350_ = v___y_308_;
goto v___jp_332_;
}
else
{
v___y_389_ = v___x_421_;
v___y_390_ = v___y_420_;
v___y_391_ = v___x_418_;
goto v___jp_388_;
}
}
else
{
v___y_414_ = v___x_421_;
v___y_415_ = v___y_420_;
v___y_416_ = v___x_424_;
v___y_417_ = v___x_418_;
goto v___jp_413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___boxed(lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_as_x27_436_, lean_object* v_b_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
size_t v___x_49382__boxed_443_; size_t v___x_49383__boxed_444_; lean_object* v_res_445_; 
v___x_49382__boxed_443_ = lean_unbox_usize(v___x_434_);
lean_dec(v___x_434_);
v___x_49383__boxed_444_ = lean_unbox_usize(v___x_435_);
lean_dec(v___x_435_);
v_res_445_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_432_, v_a_433_, v___x_49382__boxed_443_, v___x_49383__boxed_444_, v_as_x27_436_, v_b_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_as_x27_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(lean_object* v_a_446_, lean_object* v_a_447_, size_t v___x_448_, size_t v___x_449_, lean_object* v_as_450_, lean_object* v_as_x27_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
if (lean_obj_tag(v_as_x27_451_) == 0)
{
lean_object* v___x_463_; 
lean_dec_ref(v_a_447_);
lean_dec_ref(v_a_446_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_b_452_);
return v___x_463_;
}
else
{
lean_object* v_toCold_464_; lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v_currRecDepth_467_; lean_object* v_ref_468_; uint8_t v_suppressElabErrors_469_; uint8_t v_checkDeprecated_470_; uint8_t v_isRecordingDeps_471_; lean_object* v_fileName_472_; lean_object* v_fileMap_473_; lean_object* v_options_474_; lean_object* v_currNamespace_475_; lean_object* v_openDecls_476_; lean_object* v_initHeartbeats_477_; lean_object* v_maxHeartbeats_478_; lean_object* v_quotContext_479_; lean_object* v_currMacroScope_480_; lean_object* v_cancelTk_x3f_481_; lean_object* v_inheritedTraceOptions_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint16_t v___y_486_; lean_object* v___y_487_; lean_object* v_fileName_488_; lean_object* v_fileMap_489_; lean_object* v_currNamespace_490_; lean_object* v_openDecls_491_; lean_object* v_initHeartbeats_492_; lean_object* v_maxHeartbeats_493_; lean_object* v_quotContext_494_; lean_object* v_currMacroScope_495_; lean_object* v_cancelTk_x3f_496_; lean_object* v_inheritedTraceOptions_497_; lean_object* v_currRecDepth_498_; lean_object* v_ref_499_; uint8_t v_suppressElabErrors_500_; uint8_t v_checkDeprecated_501_; uint8_t v_isRecordingDeps_502_; lean_object* v___y_503_; uint8_t v___y_542_; uint16_t v___y_543_; lean_object* v___y_544_; uint8_t v___y_567_; uint16_t v___y_568_; lean_object* v___y_569_; uint8_t v___y_570_; uint8_t v___x_571_; lean_object* v___y_573_; 
v_toCold_464_ = lean_ctor_get(v___y_460_, 0);
v_head_465_ = lean_ctor_get(v_as_x27_451_, 0);
v_tail_466_ = lean_ctor_get(v_as_x27_451_, 1);
v_currRecDepth_467_ = lean_ctor_get(v___y_460_, 1);
v_ref_468_ = lean_ctor_get(v___y_460_, 2);
v_suppressElabErrors_469_ = lean_ctor_get_uint8(v___y_460_, sizeof(void*)*3 + 2);
v_checkDeprecated_470_ = lean_ctor_get_uint8(v___y_460_, sizeof(void*)*3 + 3);
v_isRecordingDeps_471_ = lean_ctor_get_uint8(v___y_460_, sizeof(void*)*3 + 4);
v_fileName_472_ = lean_ctor_get(v_toCold_464_, 0);
v_fileMap_473_ = lean_ctor_get(v_toCold_464_, 1);
v_options_474_ = lean_ctor_get(v_toCold_464_, 2);
v_currNamespace_475_ = lean_ctor_get(v_toCold_464_, 4);
v_openDecls_476_ = lean_ctor_get(v_toCold_464_, 5);
v_initHeartbeats_477_ = lean_ctor_get(v_toCold_464_, 6);
v_maxHeartbeats_478_ = lean_ctor_get(v_toCold_464_, 7);
v_quotContext_479_ = lean_ctor_get(v_toCold_464_, 8);
v_currMacroScope_480_ = lean_ctor_get(v_toCold_464_, 9);
v_cancelTk_x3f_481_ = lean_ctor_get(v_toCold_464_, 10);
v_inheritedTraceOptions_482_ = lean_ctor_get(v_toCold_464_, 11);
v___x_483_ = lean_box(0);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_usize_dec_eq(v___x_448_, v___x_449_);
if (v_isRecordingDeps_471_ == 0)
{
lean_object* v___x_583_; 
lean_inc(v_head_465_);
lean_inc_ref(v_options_474_);
v___x_583_ = lean_apply_1(v_head_465_, v_options_474_);
v___y_573_ = v___x_583_;
goto v___jp_572_;
}
else
{
lean_object* v___x_584_; 
lean_inc_ref(v_options_474_);
v___x_584_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_474_);
v___y_573_ = v___x_584_;
goto v___jp_572_;
}
v___jp_485_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = l_Lean_maxRecDepth;
v___x_505_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_487_, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_506_, 0, v_fileName_488_);
lean_ctor_set(v___x_506_, 1, v_fileMap_489_);
lean_ctor_set(v___x_506_, 2, v___y_487_);
lean_ctor_set(v___x_506_, 3, v___x_505_);
lean_ctor_set(v___x_506_, 4, v_currNamespace_490_);
lean_ctor_set(v___x_506_, 5, v_openDecls_491_);
lean_ctor_set(v___x_506_, 6, v_initHeartbeats_492_);
lean_ctor_set(v___x_506_, 7, v_maxHeartbeats_493_);
lean_ctor_set(v___x_506_, 8, v_quotContext_494_);
lean_ctor_set(v___x_506_, 9, v_currMacroScope_495_);
lean_ctor_set(v___x_506_, 10, v_cancelTk_x3f_496_);
lean_ctor_set(v___x_506_, 11, v_inheritedTraceOptions_497_);
lean_inc(v_ref_499_);
lean_inc(v_currRecDepth_498_);
v___x_507_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_currRecDepth_498_);
lean_ctor_set(v___x_507_, 2, v_ref_499_);
lean_ctor_set_uint16(v___x_507_, sizeof(void*)*3, v___y_486_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 2, v_suppressElabErrors_500_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 3, v_checkDeprecated_501_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 4, v_isRecordingDeps_502_);
lean_inc_ref(v_a_446_);
v___x_508_ = l_Lean_Meta_ppExpr(v_a_446_, v___y_458_, v___y_459_, v___x_507_, v___y_503_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
lean_inc_ref(v_a_447_);
v___x_510_ = l_Lean_Meta_ppExpr(v_a_447_, v___y_458_, v___y_459_, v___x_507_, v___y_503_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_Std_Format_defWidth;
v___x_513_ = l_Std_Format_pretty(v_a_509_, v___x_512_, v___x_484_, v___x_484_);
v___x_514_ = l_Std_Format_pretty(v_a_511_, v___x_512_, v___x_484_, v___x_484_);
v___x_515_ = lean_string_dec_eq(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_516_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_517_ = l_Lean_indentExpr(v_a_446_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_indentExpr(v_a_447_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_522_, v___y_458_, v___y_459_, v___x_507_, v___y_503_);
lean_dec_ref_known(v___x_507_, 3);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec_ref_known(v___x_507_, 3);
v___x_524_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_446_, v_a_447_, v___x_448_, v___x_449_, v_tail_466_, v___x_483_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
return v___x_524_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_509_);
lean_dec_ref_known(v___x_507_, 3);
lean_dec_ref(v_a_447_);
lean_dec_ref(v_a_446_);
v_a_525_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_510_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_510_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref_known(v___x_507_, 3);
lean_dec_ref(v_a_447_);
lean_dec_ref(v_a_446_);
v_a_533_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_508_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_508_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
v___jp_541_:
{
lean_object* v___x_545_; lean_object* v_env_546_; lean_object* v_nextMacroScope_547_; lean_object* v_ngen_548_; lean_object* v_auxDeclNGen_549_; lean_object* v_traceState_550_; lean_object* v_recordedDeps_551_; lean_object* v_messages_552_; lean_object* v_infoState_553_; lean_object* v_snapshotTasks_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v___x_545_ = lean_st_ref_take(v___y_461_);
v_env_546_ = lean_ctor_get(v___x_545_, 0);
v_nextMacroScope_547_ = lean_ctor_get(v___x_545_, 1);
v_ngen_548_ = lean_ctor_get(v___x_545_, 2);
v_auxDeclNGen_549_ = lean_ctor_get(v___x_545_, 3);
v_traceState_550_ = lean_ctor_get(v___x_545_, 4);
v_recordedDeps_551_ = lean_ctor_get(v___x_545_, 6);
v_messages_552_ = lean_ctor_get(v___x_545_, 7);
v_infoState_553_ = lean_ctor_get(v___x_545_, 8);
v_snapshotTasks_554_ = lean_ctor_get(v___x_545_, 9);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_545_, 5);
lean_dec(v_unused_565_);
v___x_556_ = v___x_545_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_snapshotTasks_554_);
lean_inc(v_infoState_553_);
lean_inc(v_messages_552_);
lean_inc(v_recordedDeps_551_);
lean_inc(v_traceState_550_);
lean_inc(v_auxDeclNGen_549_);
lean_inc(v_ngen_548_);
lean_inc(v_nextMacroScope_547_);
lean_inc(v_env_546_);
lean_dec(v___x_545_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = l_Lean_Kernel_enableDiag(v_env_546_, v___y_542_);
v___x_559_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 5, v___x_559_);
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_nextMacroScope_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_ngen_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_auxDeclNGen_549_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_traceState_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_recordedDeps_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_messages_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_infoState_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 9, v_snapshotTasks_554_);
v___x_561_ = v_reuseFailAlloc_563_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_st_ref_put(v___y_461_, v___x_561_);
lean_inc_ref(v_inheritedTraceOptions_482_);
lean_inc(v_cancelTk_x3f_481_);
lean_inc(v_currMacroScope_480_);
lean_inc(v_quotContext_479_);
lean_inc(v_maxHeartbeats_478_);
lean_inc(v_initHeartbeats_477_);
lean_inc(v_openDecls_476_);
lean_inc(v_currNamespace_475_);
lean_inc_ref(v_fileMap_473_);
lean_inc_ref(v_fileName_472_);
v___y_486_ = v___y_543_;
v___y_487_ = v___y_544_;
v_fileName_488_ = v_fileName_472_;
v_fileMap_489_ = v_fileMap_473_;
v_currNamespace_490_ = v_currNamespace_475_;
v_openDecls_491_ = v_openDecls_476_;
v_initHeartbeats_492_ = v_initHeartbeats_477_;
v_maxHeartbeats_493_ = v_maxHeartbeats_478_;
v_quotContext_494_ = v_quotContext_479_;
v_currMacroScope_495_ = v_currMacroScope_480_;
v_cancelTk_x3f_496_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_497_ = v_inheritedTraceOptions_482_;
v_currRecDepth_498_ = v_currRecDepth_467_;
v_ref_499_ = v_ref_468_;
v_suppressElabErrors_500_ = v_suppressElabErrors_469_;
v_checkDeprecated_501_ = v_checkDeprecated_470_;
v_isRecordingDeps_502_ = v_isRecordingDeps_471_;
v___y_503_ = v___y_461_;
goto v___jp_485_;
}
}
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
v___y_542_ = v___y_570_;
v___y_543_ = v___y_568_;
v___y_544_ = v___y_569_;
goto v___jp_541_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_482_);
lean_inc(v_cancelTk_x3f_481_);
lean_inc(v_currMacroScope_480_);
lean_inc(v_quotContext_479_);
lean_inc(v_maxHeartbeats_478_);
lean_inc(v_initHeartbeats_477_);
lean_inc(v_openDecls_476_);
lean_inc(v_currNamespace_475_);
lean_inc_ref(v_fileMap_473_);
lean_inc_ref(v_fileName_472_);
v___y_486_ = v___y_568_;
v___y_487_ = v___y_569_;
v_fileName_488_ = v_fileName_472_;
v_fileMap_489_ = v_fileMap_473_;
v_currNamespace_490_ = v_currNamespace_475_;
v_openDecls_491_ = v_openDecls_476_;
v_initHeartbeats_492_ = v_initHeartbeats_477_;
v_maxHeartbeats_493_ = v_maxHeartbeats_478_;
v_quotContext_494_ = v_quotContext_479_;
v_currMacroScope_495_ = v_currMacroScope_480_;
v_cancelTk_x3f_496_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_497_ = v_inheritedTraceOptions_482_;
v_currRecDepth_498_ = v_currRecDepth_467_;
v_ref_499_ = v_ref_468_;
v_suppressElabErrors_500_ = v_suppressElabErrors_469_;
v_checkDeprecated_501_ = v_checkDeprecated_470_;
v_isRecordingDeps_502_ = v_isRecordingDeps_471_;
v___y_503_ = v___y_461_;
goto v___jp_485_;
}
}
v___jp_572_:
{
uint16_t v___x_574_; lean_object* v___x_575_; lean_object* v_env_576_; uint8_t v___x_577_; uint16_t v___x_578_; uint16_t v___x_579_; uint16_t v___x_580_; uint8_t v___x_581_; 
v___x_574_ = l_Lean_OptionFlags_ofOptions(v___y_573_);
v___x_575_ = lean_st_ref_get(v___y_461_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_576_);
lean_dec_ref(v_env_576_);
v___x_578_ = 512;
v___x_579_ = lean_uint16_land(v___x_574_, v___x_578_);
v___x_580_ = 0;
v___x_581_ = lean_uint16_dec_eq(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = 1;
v___y_567_ = v___x_577_;
v___y_568_ = v___x_574_;
v___y_569_ = v___y_573_;
v___y_570_ = v___x_582_;
goto v___jp_566_;
}
else
{
if (v___x_571_ == 0)
{
if (v___x_577_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_482_);
lean_inc(v_cancelTk_x3f_481_);
lean_inc(v_currMacroScope_480_);
lean_inc(v_quotContext_479_);
lean_inc(v_maxHeartbeats_478_);
lean_inc(v_initHeartbeats_477_);
lean_inc(v_openDecls_476_);
lean_inc(v_currNamespace_475_);
lean_inc_ref(v_fileMap_473_);
lean_inc_ref(v_fileName_472_);
v___y_486_ = v___x_574_;
v___y_487_ = v___y_573_;
v_fileName_488_ = v_fileName_472_;
v_fileMap_489_ = v_fileMap_473_;
v_currNamespace_490_ = v_currNamespace_475_;
v_openDecls_491_ = v_openDecls_476_;
v_initHeartbeats_492_ = v_initHeartbeats_477_;
v_maxHeartbeats_493_ = v_maxHeartbeats_478_;
v_quotContext_494_ = v_quotContext_479_;
v_currMacroScope_495_ = v_currMacroScope_480_;
v_cancelTk_x3f_496_ = v_cancelTk_x3f_481_;
v_inheritedTraceOptions_497_ = v_inheritedTraceOptions_482_;
v_currRecDepth_498_ = v_currRecDepth_467_;
v_ref_499_ = v_ref_468_;
v_suppressElabErrors_500_ = v_suppressElabErrors_469_;
v_checkDeprecated_501_ = v_checkDeprecated_470_;
v_isRecordingDeps_502_ = v_isRecordingDeps_471_;
v___y_503_ = v___y_461_;
goto v___jp_485_;
}
else
{
v___y_542_ = v___x_571_;
v___y_543_ = v___x_574_;
v___y_544_ = v___y_573_;
goto v___jp_541_;
}
}
else
{
v___y_567_ = v___x_577_;
v___y_568_ = v___x_574_;
v___y_569_ = v___y_573_;
v___y_570_ = v___x_571_;
goto v___jp_566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_a_585_ = _args[0];
lean_object* v_a_586_ = _args[1];
lean_object* v___x_587_ = _args[2];
lean_object* v___x_588_ = _args[3];
lean_object* v_as_589_ = _args[4];
lean_object* v_as_x27_590_ = _args[5];
lean_object* v_b_591_ = _args[6];
lean_object* v___y_592_ = _args[7];
lean_object* v___y_593_ = _args[8];
lean_object* v___y_594_ = _args[9];
lean_object* v___y_595_ = _args[10];
lean_object* v___y_596_ = _args[11];
lean_object* v___y_597_ = _args[12];
lean_object* v___y_598_ = _args[13];
lean_object* v___y_599_ = _args[14];
lean_object* v___y_600_ = _args[15];
lean_object* v___y_601_ = _args[16];
_start:
{
size_t v___x_49608__boxed_602_; size_t v___x_49609__boxed_603_; lean_object* v_res_604_; 
v___x_49608__boxed_602_ = lean_unbox_usize(v___x_587_);
lean_dec(v___x_587_);
v___x_49609__boxed_603_ = lean_unbox_usize(v___x_588_);
lean_dec(v___x_588_);
v_res_604_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_585_, v_a_586_, v___x_49608__boxed_602_, v___x_49609__boxed_603_, v_as_589_, v_as_x27_590_, v_b_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec(v_as_x27_590_);
lean_dec(v_as_589_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(uint8_t v___y_605_, lean_object* v_a_606_, lean_object* v___f_607_, lean_object* v___f_608_, lean_object* v___f_609_, uint8_t v___x_610_, lean_object* v___x_611_, uint8_t v___x_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
switch(v___y_605_)
{
case 0:
{
lean_object* v___x_623_; 
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v___x_623_ = l_Lean_Meta_Grind_normLegacy(v_a_606_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
case 1:
{
lean_object* v___x_624_; 
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v___x_624_ = l_Lean_Meta_Grind_normSym___redArg(v_a_606_, v___y_614_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_624_;
}
default: 
{
lean_object* v___x_625_; 
lean_inc_ref(v_a_606_);
v___x_625_ = l_Lean_Meta_Grind_normLegacy(v_a_606_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l_Lean_Meta_Grind_normSym___redArg(v_a_606_, v___y_614_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_expr_629_; lean_object* v___x_630_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v_expr_629_ = lean_ctor_get(v_a_626_, 0);
lean_inc_ref(v_expr_629_);
v___x_630_ = l_Lean_Meta_Sym_shareCommon(v_expr_629_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_expr_632_; lean_object* v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v_expr_632_ = lean_ctor_get(v_a_628_, 0);
lean_inc_ref(v_expr_632_);
lean_dec(v_a_628_);
v___x_633_ = l_Lean_Meta_Sym_shareCommon(v_expr_632_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_710_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_710_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_710_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_710_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
size_t v___x_638_; size_t v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_ptr_addr(v_a_631_);
v___x_639_ = lean_ptr_addr(v_a_634_);
v___x_640_ = lean_usize_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___x_674_; 
lean_del_object(v___x_636_);
lean_dec(v_a_626_);
lean_inc(v_a_631_);
v___x_674_ = l_Lean_Meta_ppExpr(v_a_631_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
lean_inc(v_a_634_);
v___x_676_ = l_Lean_Meta_ppExpr(v_a_634_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Std_Format_defWidth;
lean_inc_n(v___x_611_, 3);
v___x_679_ = l_Std_Format_pretty(v_a_675_, v___x_678_, v___x_611_, v___x_611_);
v___x_680_ = l_Std_Format_pretty(v_a_677_, v___x_678_, v___x_611_, v___x_611_);
v___x_681_ = lean_string_dec_eq(v___x_679_, v___x_680_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_679_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v___x_682_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_631_, v_a_634_, v___x_612_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
v___y_642_ = v___y_613_;
v___y_643_ = v___y_614_;
v___y_644_ = v___y_615_;
v___y_645_ = v___y_616_;
v___y_646_ = v___y_617_;
v___y_647_ = v___y_618_;
v___y_648_ = v___y_619_;
v___y_649_ = v___y_620_;
v___y_650_ = v___y_621_;
goto v___jp_641_;
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_675_);
lean_dec(v_a_634_);
lean_dec(v_a_631_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v_a_691_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_676_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_676_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_634_);
lean_dec(v_a_631_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v_a_699_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_674_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_674_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
v___jp_641_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v___f_607_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___f_608_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___f_609_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_box(0);
lean_inc(v_a_634_);
lean_inc(v_a_631_);
v___x_656_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_631_, v_a_634_, v___x_638_, v___x_639_, v___x_654_, v___x_654_, v___x_655_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec_ref_known(v___x_654_, 2);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref_known(v___x_656_, 1);
v___x_657_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_631_, v_a_634_, v___x_610_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_a_634_);
lean_dec(v_a_631_);
v_a_666_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_656_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_656_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v_a_634_);
lean_dec(v_a_631_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_a_626_);
v___x_708_ = v___x_636_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_626_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_631_);
lean_dec(v_a_626_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v_a_711_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_633_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_633_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_628_);
lean_dec(v_a_626_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
v_a_719_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_630_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_630_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_dec(v_a_626_);
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
return v___x_627_;
}
}
else
{
lean_dec(v___x_611_);
lean_dec_ref(v___f_609_);
lean_dec_ref(v___f_608_);
lean_dec_ref(v___f_607_);
lean_dec_ref(v_a_606_);
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed(lean_object** _args){
lean_object* v___y_727_ = _args[0];
lean_object* v_a_728_ = _args[1];
lean_object* v___f_729_ = _args[2];
lean_object* v___f_730_ = _args[3];
lean_object* v___f_731_ = _args[4];
lean_object* v___x_732_ = _args[5];
lean_object* v___x_733_ = _args[6];
lean_object* v___x_734_ = _args[7];
lean_object* v___y_735_ = _args[8];
lean_object* v___y_736_ = _args[9];
lean_object* v___y_737_ = _args[10];
lean_object* v___y_738_ = _args[11];
lean_object* v___y_739_ = _args[12];
lean_object* v___y_740_ = _args[13];
lean_object* v___y_741_ = _args[14];
lean_object* v___y_742_ = _args[15];
lean_object* v___y_743_ = _args[16];
lean_object* v___y_744_ = _args[17];
_start:
{
uint8_t v___y_49820__boxed_745_; uint8_t v___x_49825__boxed_746_; uint8_t v___x_49827__boxed_747_; lean_object* v_res_748_; 
v___y_49820__boxed_745_ = lean_unbox(v___y_727_);
v___x_49825__boxed_746_ = lean_unbox(v___x_732_);
v___x_49827__boxed_747_ = lean_unbox(v___x_734_);
v_res_748_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(v___y_49820__boxed_745_, v_a_728_, v___f_729_, v___f_730_, v___f_731_, v___x_49825__boxed_746_, v___x_733_, v___x_49827__boxed_747_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___y_761_; lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_751_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; uint8_t v___y_773_; uint8_t v_reducible_792_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v_reducible_792_ = lean_ctor_get_uint8(v_a_771_, sizeof(void*)*17 + 33);
lean_dec(v_a_771_);
if (v_reducible_792_ == 0)
{
uint8_t v___x_793_; 
v___x_793_ = 1;
v___y_773_ = v___x_793_;
goto v___jp_772_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 2;
v___y_773_ = v___x_794_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_774_; uint8_t v_transparency_775_; uint8_t v___x_776_; 
v___x_774_ = l_Lean_Meta_Context_config(v___y_755_);
v_transparency_775_ = lean_ctor_get_uint8(v___x_774_, 9);
lean_dec_ref(v___x_774_);
v___x_776_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_775_, v___y_773_);
if (v___x_776_ == 0)
{
lean_object* v_keyedConfig_777_; uint8_t v_trackZetaDelta_778_; lean_object* v_zetaDeltaSet_779_; lean_object* v_lctx_780_; lean_object* v_localInstances_781_; lean_object* v_defEqCtx_x3f_782_; lean_object* v_synthPendingDepth_783_; lean_object* v_customCanUnfoldPredicate_x3f_784_; uint8_t v_univApprox_785_; uint8_t v_inTypeClassResolution_786_; uint8_t v_cacheInferType_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_keyedConfig_777_ = lean_ctor_get(v___y_755_, 0);
v_trackZetaDelta_778_ = lean_ctor_get_uint8(v___y_755_, sizeof(void*)*7);
v_zetaDeltaSet_779_ = lean_ctor_get(v___y_755_, 1);
v_lctx_780_ = lean_ctor_get(v___y_755_, 2);
v_localInstances_781_ = lean_ctor_get(v___y_755_, 3);
v_defEqCtx_x3f_782_ = lean_ctor_get(v___y_755_, 4);
v_synthPendingDepth_783_ = lean_ctor_get(v___y_755_, 5);
v_customCanUnfoldPredicate_x3f_784_ = lean_ctor_get(v___y_755_, 6);
v_univApprox_785_ = lean_ctor_get_uint8(v___y_755_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_786_ = lean_ctor_get_uint8(v___y_755_, sizeof(void*)*7 + 2);
v_cacheInferType_787_ = lean_ctor_get_uint8(v___y_755_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_777_);
v___x_788_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_773_, v_keyedConfig_777_);
lean_inc(v_customCanUnfoldPredicate_x3f_784_);
lean_inc(v_synthPendingDepth_783_);
lean_inc(v_defEqCtx_x3f_782_);
lean_inc_ref(v_localInstances_781_);
lean_inc_ref(v_lctx_780_);
lean_inc(v_zetaDeltaSet_779_);
v___x_789_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_zetaDeltaSet_779_);
lean_ctor_set(v___x_789_, 2, v_lctx_780_);
lean_ctor_set(v___x_789_, 3, v_localInstances_781_);
lean_ctor_set(v___x_789_, 4, v_defEqCtx_x3f_782_);
lean_ctor_set(v___x_789_, 5, v_synthPendingDepth_783_);
lean_ctor_set(v___x_789_, 6, v_customCanUnfoldPredicate_x3f_784_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7, v_trackZetaDelta_778_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 1, v_univApprox_785_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 2, v_inTypeClassResolution_786_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 3, v_cacheInferType_787_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_790_ = lean_apply_10(v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___x_789_, v___y_756_, v___y_757_, v___y_758_, lean_box(0));
v___y_761_ = v___x_790_;
goto v___jp_760_;
}
else
{
lean_object* v___x_791_; 
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_791_ = lean_apply_10(v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, lean_box(0));
v___y_761_ = v___x_791_;
goto v___jp_760_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___y_749_);
v_a_795_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_770_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_770_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
v___jp_760_:
{
if (lean_obj_tag(v___y_761_) == 0)
{
return v___y_761_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___y_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___y_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___y_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___y_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed(lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(lean_object* v___x_816_, lean_object* v___x_817_, uint8_t v___x_818_, lean_object* v___f_819_, lean_object* v___f_820_, lean_object* v___f_821_, lean_object* v___x_822_, uint8_t v___x_823_, lean_object* v_stx_824_, lean_object* v___x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Elab_Tactic_elabGrindConfig___redArg(v___x_816_, v___x_817_, v___x_818_, v___y_826_, v___y_828_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; uint8_t v___y_838_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_900_ = l_Lean_Syntax_getArg(v_stx_824_, v___x_825_);
v___x_901_ = l_Lean_Syntax_getOptional_x3f(v___x_900_);
lean_dec(v___x_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
uint8_t v___x_902_; 
v___x_902_ = 0;
v___y_838_ = v___x_902_;
goto v___jp_837_;
}
else
{
lean_object* v_val_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_val_903_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v___x_901_, 1);
v___x_904_ = l_Lean_Syntax_getArg(v_val_903_, v___x_822_);
lean_dec(v_val_903_);
v___x_905_ = l_Lean_Syntax_getAtomVal(v___x_904_);
lean_dec(v___x_904_);
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0));
v___x_907_ = lean_string_dec_eq(v___x_905_, v___x_906_);
lean_dec_ref(v___x_905_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
v___x_908_ = 2;
v___y_838_ = v___x_908_;
goto v___jp_837_;
}
else
{
uint8_t v___x_909_; 
v___x_909_ = 1;
v___y_838_ = v___x_909_;
goto v___jp_837_;
}
}
v___jp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_827_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_n(v_a_840_, 2);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = l_Lean_MVarId_getType(v_a_840_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___y_848_; lean_object* v___f_849_; lean_object* v___x_850_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_a_842_, v___y_831_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_n(v_a_844_, 2);
lean_dec_ref(v___x_843_);
v___x_845_ = lean_box(v___y_838_);
v___x_846_ = lean_box(v___x_818_);
v___x_847_ = lean_box(v___x_823_);
v___y_848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed), 18, 8);
lean_closure_set(v___y_848_, 0, v___x_845_);
lean_closure_set(v___y_848_, 1, v_a_844_);
lean_closure_set(v___y_848_, 2, v___f_819_);
lean_closure_set(v___y_848_, 3, v___f_820_);
lean_closure_set(v___y_848_, 4, v___f_821_);
lean_closure_set(v___y_848_, 5, v___x_846_);
lean_closure_set(v___y_848_, 6, v___x_822_);
lean_closure_set(v___y_848_, 7, v___x_847_);
v___f_849_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed), 11, 1);
lean_closure_set(v___f_849_, 0, v___y_848_);
v___x_850_ = l_Lean_Meta_Grind_mkDefaultParams(v_a_836_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_box(0);
v___x_853_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_849_, v_a_851_, v___x_852_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_Meta_applySimpResultToTarget(v_a_840_, v_a_844_, v_a_854_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v_a_844_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_858_, v___y_827_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_859_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_855_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_855_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_844_);
lean_dec(v_a_840_);
v_a_868_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_853_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_853_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___f_849_);
lean_dec(v_a_844_);
lean_dec(v_a_840_);
v_a_876_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_850_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_850_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_840_);
lean_dec(v_a_836_);
lean_dec(v___x_822_);
lean_dec_ref(v___f_821_);
lean_dec_ref(v___f_820_);
lean_dec_ref(v___f_819_);
v_a_884_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_841_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_841_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_836_);
lean_dec(v___x_822_);
lean_dec_ref(v___f_821_);
lean_dec_ref(v___f_820_);
lean_dec_ref(v___f_819_);
v_a_892_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_839_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_839_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___x_822_);
lean_dec_ref(v___f_821_);
lean_dec_ref(v___f_820_);
lean_dec_ref(v___f_819_);
v_a_910_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_835_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_835_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed(lean_object** _args){
lean_object* v___x_918_ = _args[0];
lean_object* v___x_919_ = _args[1];
lean_object* v___x_920_ = _args[2];
lean_object* v___f_921_ = _args[3];
lean_object* v___f_922_ = _args[4];
lean_object* v___f_923_ = _args[5];
lean_object* v___x_924_ = _args[6];
lean_object* v___x_925_ = _args[7];
lean_object* v_stx_926_ = _args[8];
lean_object* v___x_927_ = _args[9];
lean_object* v___y_928_ = _args[10];
lean_object* v___y_929_ = _args[11];
lean_object* v___y_930_ = _args[12];
lean_object* v___y_931_ = _args[13];
lean_object* v___y_932_ = _args[14];
lean_object* v___y_933_ = _args[15];
lean_object* v___y_934_ = _args[16];
lean_object* v___y_935_ = _args[17];
lean_object* v___y_936_ = _args[18];
_start:
{
uint8_t v___x_50181__boxed_937_; uint8_t v___x_50186__boxed_938_; lean_object* v_res_939_; 
v___x_50181__boxed_937_ = lean_unbox(v___x_920_);
v___x_50186__boxed_938_ = lean_unbox(v___x_925_);
v_res_939_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(v___x_918_, v___x_919_, v___x_50181__boxed_937_, v___f_921_, v___f_922_, v___f_923_, v___x_924_, v___x_50186__boxed_938_, v_stx_926_, v___x_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___x_927_);
lean_dec(v_stx_926_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(lean_object* v_stx_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; uint8_t v___x_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___f_990_; lean_object* v___x_991_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = l_Lean_Syntax_getArg(v_stx_968_, v___x_978_);
v___x_980_ = 0;
v___x_981_ = 1;
v___f_982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0));
v___f_983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1));
v___f_984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2));
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_unsigned_to_nat(2u);
v___x_987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3));
v___x_988_ = lean_box(v___x_981_);
v___x_989_ = lean_box(v___x_980_);
v___f_990_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed), 19, 10);
lean_closure_set(v___f_990_, 0, v___x_979_);
lean_closure_set(v___f_990_, 1, v___x_987_);
lean_closure_set(v___f_990_, 2, v___x_988_);
lean_closure_set(v___f_990_, 3, v___f_984_);
lean_closure_set(v___f_990_, 4, v___f_983_);
lean_closure_set(v___f_990_, 5, v___f_982_);
lean_closure_set(v___f_990_, 6, v___x_985_);
lean_closure_set(v___f_990_, 7, v___x_989_);
lean_closure_set(v___f_990_, 8, v_stx_968_);
lean_closure_set(v___f_990_, 9, v___x_986_);
v___x_991_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_990_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed(lean_object* v_stx_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(v_stx_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(lean_object* v_00_u03b1_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(v_00_u03b1_1011_, v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(lean_object* v_a_1019_, lean_object* v_a_1020_, size_t v___x_1021_, size_t v___x_1022_, lean_object* v_as_1023_, lean_object* v_as_x27_1024_, lean_object* v_b_1025_, lean_object* v_a_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_1019_, v_a_1020_, v___x_1021_, v___x_1022_, v_as_1023_, v_as_x27_1024_, v_b_1025_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___boxed(lean_object** _args){
lean_object* v_a_1038_ = _args[0];
lean_object* v_a_1039_ = _args[1];
lean_object* v___x_1040_ = _args[2];
lean_object* v___x_1041_ = _args[3];
lean_object* v_as_1042_ = _args[4];
lean_object* v_as_x27_1043_ = _args[5];
lean_object* v_b_1044_ = _args[6];
lean_object* v_a_1045_ = _args[7];
lean_object* v___y_1046_ = _args[8];
lean_object* v___y_1047_ = _args[9];
lean_object* v___y_1048_ = _args[10];
lean_object* v___y_1049_ = _args[11];
lean_object* v___y_1050_ = _args[12];
lean_object* v___y_1051_ = _args[13];
lean_object* v___y_1052_ = _args[14];
lean_object* v___y_1053_ = _args[15];
lean_object* v___y_1054_ = _args[16];
lean_object* v___y_1055_ = _args[17];
_start:
{
size_t v___x_50603__boxed_1056_; size_t v___x_50604__boxed_1057_; lean_object* v_res_1058_; 
v___x_50603__boxed_1056_ = lean_unbox_usize(v___x_1040_);
lean_dec(v___x_1040_);
v___x_50604__boxed_1057_ = lean_unbox_usize(v___x_1041_);
lean_dec(v___x_1041_);
v_res_1058_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(v_a_1038_, v_a_1039_, v___x_50603__boxed_1056_, v___x_50604__boxed_1057_, v_as_1042_, v_as_x27_1043_, v_b_1044_, v_a_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v_as_x27_1043_);
lean_dec(v_as_1042_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(lean_object* v_a_1059_, lean_object* v_a_1060_, size_t v___x_1061_, size_t v___x_1062_, lean_object* v_as_1063_, lean_object* v_as_x27_1064_, lean_object* v_b_1065_, lean_object* v_a_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_1059_, v_a_1060_, v___x_1061_, v___x_1062_, v_as_x27_1064_, v_b_1065_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_a_1078_ = _args[0];
lean_object* v_a_1079_ = _args[1];
lean_object* v___x_1080_ = _args[2];
lean_object* v___x_1081_ = _args[3];
lean_object* v_as_1082_ = _args[4];
lean_object* v_as_x27_1083_ = _args[5];
lean_object* v_b_1084_ = _args[6];
lean_object* v_a_1085_ = _args[7];
lean_object* v___y_1086_ = _args[8];
lean_object* v___y_1087_ = _args[9];
lean_object* v___y_1088_ = _args[10];
lean_object* v___y_1089_ = _args[11];
lean_object* v___y_1090_ = _args[12];
lean_object* v___y_1091_ = _args[13];
lean_object* v___y_1092_ = _args[14];
lean_object* v___y_1093_ = _args[15];
lean_object* v___y_1094_ = _args[16];
lean_object* v___y_1095_ = _args[17];
_start:
{
size_t v___x_50650__boxed_1096_; size_t v___x_50651__boxed_1097_; lean_object* v_res_1098_; 
v___x_50650__boxed_1096_ = lean_unbox_usize(v___x_1080_);
lean_dec(v___x_1080_);
v___x_50651__boxed_1097_ = lean_unbox_usize(v___x_1081_);
lean_dec(v___x_1081_);
v_res_1098_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(v_a_1078_, v_a_1079_, v___x_50650__boxed_1096_, v___x_50651__boxed_1097_, v_as_1082_, v_as_x27_1083_, v_b_1084_, v_a_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_as_x27_1083_);
lean_dec(v_as_1082_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1(){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1147_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4));
v___x_1149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20));
v___x_1150_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed), 10, 0);
v___x_1151_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1147_, v___x_1148_, v___x_1149_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___boxed(lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
return v_res_1153_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Norm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Norm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Norm(builtin);
}
#ifdef __cplusplus
}
#endif

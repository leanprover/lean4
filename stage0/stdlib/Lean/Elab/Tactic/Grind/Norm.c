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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg(lean_object* v_legacy_24_){
_start:
{
lean_inc(v_legacy_24_);
return v_legacy_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg___boxed(lean_object* v_legacy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___redArg(v_legacy_25_);
lean_dec(v_legacy_25_);
return v_res_26_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_legacy_30_){
_start:
{
lean_inc(v_legacy_30_);
return v_legacy_30_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_legacy_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(lean_box(0), v_t_28_, lean_box(0), v_legacy_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_legacy_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_legacy_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_legacy_35_);
lean_dec(v_legacy_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg(lean_object* v_sym_38_){
_start:
{
lean_inc(v_sym_38_);
return v_sym_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg___boxed(lean_object* v_sym_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___redArg(v_sym_39_);
lean_dec(v_sym_39_);
return v_res_40_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_sym_44_){
_start:
{
lean_inc(v_sym_44_);
return v_sym_44_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_sym_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(lean_box(0), v_t_42_, lean_box(0), v_sym_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_sym_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_sym_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_sym_49_);
lean_dec(v_sym_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg(lean_object* v_check_52_){
_start:
{
lean_inc(v_check_52_);
return v_check_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg___boxed(lean_object* v_check_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___redArg(v_check_53_);
lean_dec(v_check_53_);
return v_res_54_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_check_58_){
_start:
{
lean_inc(v_check_58_);
return v_check_58_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_check_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(lean_box(0), v_t_56_, lean_box(0), v_check_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_check_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_NormMode_check_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_check_63_);
lean_dec(v_check_63_);
return v_res_65_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(lean_object* v_e_66_, lean_object* v___y_67_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Expr_hasMVar(v_e_66_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v_e_66_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v_mctx_72_; lean_object* v___x_73_; lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v___x_76_; lean_object* v_cache_77_; lean_object* v_zetaDeltaFVarIds_78_; lean_object* v_postponed_79_; lean_object* v_diag_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v___x_71_ = lean_st_ref_get(v___y_67_);
v_mctx_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_mctx_72_);
lean_dec(v___x_71_);
v___x_73_ = l_Lean_instantiateMVarsCore(v_mctx_72_, v_e_66_);
v_fst_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_fst_74_);
v_snd_75_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_snd_75_);
lean_dec_ref(v___x_73_);
v___x_76_ = lean_st_ref_take(v___y_67_);
v_cache_77_ = lean_ctor_get(v___x_76_, 1);
v_zetaDeltaFVarIds_78_ = lean_ctor_get(v___x_76_, 2);
v_postponed_79_ = lean_ctor_get(v___x_76_, 3);
v_diag_80_ = lean_ctor_get(v___x_76_, 4);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v___x_76_, 0);
lean_dec(v_unused_90_);
v___x_82_ = v___x_76_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_diag_80_);
lean_inc(v_postponed_79_);
lean_inc(v_zetaDeltaFVarIds_78_);
lean_inc(v_cache_77_);
lean_dec(v___x_76_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v_snd_75_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_snd_75_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_cache_77_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_zetaDeltaFVarIds_78_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_postponed_79_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v_diag_80_);
v___x_85_ = v_reuseFailAlloc_88_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_st_ref_put(v___y_67_, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_fst_74_);
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_66_ = stack[0].m_obj;
lean_object* v___y_67_ = stack[1].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_e_66_, v___y_67_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg___boxed(lean_object* v_e_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_e_92_, v___y_93_);
lean_dec(v___y_93_);
return v_res_95_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(lean_object* v_e_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_e_96_, v___y_102_);
return v___x_106_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_96_ = stack[0].m_obj;
lean_object* v___y_97_ = stack[1].m_obj;
lean_object* v___y_98_ = stack[2].m_obj;
lean_object* v___y_99_ = stack[3].m_obj;
lean_object* v___y_100_ = stack[4].m_obj;
lean_object* v___y_101_ = stack[5].m_obj;
lean_object* v___y_102_ = stack[6].m_obj;
lean_object* v___y_103_ = stack[7].m_obj;
lean_object* v___y_104_ = stack[8].m_obj;
lean_object* v_res_107_;
v_res_107_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(v_e_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___boxed(lean_object* v_e_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1(v_e_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(lean_object* v_opts_119_, lean_object* v_opt_120_){
_start:
{
lean_object* v_name_121_; lean_object* v_defValue_122_; lean_object* v_map_123_; lean_object* v___x_124_; 
v_name_121_ = lean_ctor_get(v_opt_120_, 0);
v_defValue_122_ = lean_ctor_get(v_opt_120_, 1);
v_map_123_ = lean_ctor_get(v_opts_119_, 0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_123_, v_name_121_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_inc(v_defValue_122_);
return v_defValue_122_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v___x_124_, 1);
if (lean_obj_tag(v_val_125_) == 3)
{
lean_object* v_v_126_; 
v_v_126_ = lean_ctor_get(v_val_125_, 0);
lean_inc(v_v_126_);
lean_dec_ref_known(v_val_125_, 1);
return v_v_126_;
}
else
{
lean_dec(v_val_125_);
lean_inc(v_defValue_122_);
return v_defValue_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3___boxed(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v_opts_127_, v_opt_128_);
lean_dec_ref(v_opt_128_);
lean_dec_ref(v_opts_127_);
return v_res_129_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(lean_object* v_o_133_, lean_object* v_k_134_, uint8_t v_v_135_){
_start:
{
lean_object* v_map_136_; uint8_t v_hasTrace_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_151_; 
v_map_136_ = lean_ctor_get(v_o_133_, 0);
v_hasTrace_137_ = lean_ctor_get_uint8(v_o_133_, sizeof(void*)*1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_o_133_);
if (v_isSharedCheck_151_ == 0)
{
v___x_139_ = v_o_133_;
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_map_136_);
lean_dec(v_o_133_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_141_, 0, v_v_135_);
lean_inc(v_k_134_);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_134_, v___x_141_, v_map_136_);
if (v_hasTrace_137_ == 0)
{
lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_146_; 
v___x_143_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___closed__1));
v___x_144_ = l_Lean_Name_isPrefixOf(v___x_143_, v_k_134_);
lean_dec(v_k_134_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_146_ = v___x_139_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_142_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_144_);
return v___x_146_;
}
}
else
{
lean_object* v___x_149_; 
lean_dec(v_k_134_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_149_ = v___x_139_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_150_, sizeof(void*)*1, v_hasTrace_137_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_133_ = stack[0].m_obj;
lean_object* v_k_134_ = stack[1].m_obj;
uint8_t v_v_135_ = stack[2].m_num;
lean_object* v_res_152_;
v_res_152_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(v_o_133_, v_k_134_, v_v_135_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0___boxed(lean_object* v_o_153_, lean_object* v_k_154_, lean_object* v_v_155_){
_start:
{
uint8_t v_v_boxed_156_; lean_object* v_res_157_; 
v_v_boxed_156_ = lean_unbox(v_v_155_);
v_res_157_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(v_o_153_, v_k_154_, v_v_boxed_156_);
return v_res_157_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(lean_object* v_opts_158_, lean_object* v_opt_159_, uint8_t v_val_160_){
_start:
{
lean_object* v_name_161_; lean_object* v___x_162_; 
v_name_161_ = lean_ctor_get(v_opt_159_, 0);
lean_inc(v_name_161_);
lean_dec_ref(v_opt_159_);
v___x_162_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_spec__0(v_opts_158_, v_name_161_, v_val_160_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_158_ = stack[0].m_obj;
lean_object* v_opt_159_ = stack[1].m_obj;
uint8_t v_val_160_ = stack[2].m_num;
lean_object* v_res_163_;
v_res_163_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_opts_158_, v_opt_159_, v_val_160_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0___boxed(lean_object* v_opts_164_, lean_object* v_opt_165_, lean_object* v_val_166_){
_start:
{
uint8_t v_val_boxed_167_; lean_object* v_res_168_; 
v_val_boxed_167_ = lean_unbox(v_val_166_);
v_res_168_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_opts_164_, v_opt_165_, v_val_boxed_167_);
return v_res_168_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(uint8_t v___x_169_, uint8_t v___x_170_, lean_object* v_o_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = l_Lean_pp_funBinderTypes;
v___x_173_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_o_171_, v___x_172_, v___x_169_);
v___x_174_ = l_Lean_pp_match;
v___x_175_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v___x_173_, v___x_174_, v___x_170_);
return v___x_175_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_169_ = stack[0].m_num;
uint8_t v___x_170_ = stack[1].m_num;
lean_object* v_o_171_ = stack[2].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(v___x_169_, v___x_170_, v_o_171_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0___boxed(lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v_o_179_){
_start:
{
uint8_t v___x_49277__boxed_180_; uint8_t v___x_49278__boxed_181_; lean_object* v_res_182_; 
v___x_49277__boxed_180_ = lean_unbox(v___x_177_);
v___x_49278__boxed_181_ = lean_unbox(v___x_178_);
v_res_182_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(v___x_49277__boxed_180_, v___x_49278__boxed_181_, v_o_179_);
return v_res_182_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(uint8_t v___x_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = l_Lean_pp_explicit;
v___x_186_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_x_184_, v___x_185_, v___x_183_);
return v___x_186_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_183_ = stack[0].m_num;
lean_object* v_x_184_ = stack[1].m_obj;
lean_object* v_res_187_;
v_res_187_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(v___x_183_, v_x_184_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1___boxed(lean_object* v___x_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_49299__boxed_190_; lean_object* v_res_191_; 
v___x_49299__boxed_190_ = lean_unbox(v___x_188_);
v_res_191_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(v___x_49299__boxed_190_, v_x_189_);
return v_res_191_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(uint8_t v___x_192_, lean_object* v___f_193_, lean_object* v_o_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = l_Lean_pp_explicit;
v___x_196_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__0(v_o_194_, v___x_195_, v___x_192_);
v___x_197_ = lean_apply_1(v___f_193_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_192_ = stack[0].m_num;
lean_object* v___f_193_ = stack[1].m_obj;
lean_object* v_o_194_ = stack[2].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(v___x_192_, v___f_193_, v_o_194_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2___boxed(lean_object* v___x_199_, lean_object* v___f_200_, lean_object* v_o_201_){
_start:
{
uint8_t v___x_49315__boxed_202_; lean_object* v_res_203_; 
v___x_49315__boxed_202_ = lean_unbox(v___x_199_);
v_res_203_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(v___x_49315__boxed_202_, v___f_200_, v_o_201_);
return v_res_203_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(lean_object* v_msgData_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_env_211_; uint8_t v___x_212_; lean_object* v_env_213_; lean_object* v___x_214_; lean_object* v_toCold_215_; lean_object* v_mctx_216_; lean_object* v_lctx_217_; lean_object* v_options_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_210_ = lean_st_ref_get(v___y_208_);
v_env_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_env_211_);
lean_dec(v___x_210_);
v___x_212_ = 0;
v_env_213_ = l_Lean_Environment_setRecordingDeps(v_env_211_, v___x_212_);
v___x_214_ = lean_st_ref_get(v___y_206_);
v_toCold_215_ = lean_ctor_get(v___y_207_, 0);
v_mctx_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_mctx_216_);
lean_dec(v___x_214_);
v_lctx_217_ = lean_ctor_get(v___y_205_, 2);
v_options_218_ = lean_ctor_get(v_toCold_215_, 2);
lean_inc_ref(v_options_218_);
lean_inc_ref(v_lctx_217_);
v___x_219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_219_, 0, v_env_213_);
lean_ctor_set(v___x_219_, 1, v_mctx_216_);
lean_ctor_set(v___x_219_, 2, v_lctx_217_);
lean_ctor_set(v___x_219_, 3, v_options_218_);
v___x_220_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_msgData_204_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_204_ = stack[0].m_obj;
lean_object* v___y_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v___y_207_ = stack[3].m_obj;
lean_object* v___y_208_ = stack[4].m_obj;
lean_object* v_res_222_;
v_res_222_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(v_msgData_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3___boxed(lean_object* v_msgData_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(v_msgData_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_ref_236_; lean_object* v___x_237_; lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
v_ref_236_ = lean_ctor_get(v___y_233_, 2);
v___x_237_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_spec__3(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_inc(v_ref_236_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_ref_236_);
lean_ctor_set(v___x_242_, 1, v_a_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 1);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_230_ = stack[0].m_obj;
lean_object* v___y_231_ = stack[1].m_obj;
lean_object* v___y_232_ = stack[2].m_obj;
lean_object* v___y_233_ = stack[3].m_obj;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v_res_247_;
v_res_247_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg___boxed(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__0));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__2));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__4));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(lean_object* v_a_266_, lean_object* v_a_267_, uint8_t v_hidden_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___y_275_; 
if (v_hidden_268_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__6));
v___y_275_ = v___x_288_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7));
v___y_275_ = v___x_289_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1);
lean_inc_ref(v___y_275_);
v___x_277_ = l_Lean_stringToMessageData(v___y_275_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_indentExpr(v_a_266_);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_indentExpr(v_a_267_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_286_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
return v___x_287_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_266_ = stack[0].m_obj;
lean_object* v_a_267_ = stack[1].m_obj;
uint8_t v_hidden_268_ = stack[2].m_num;
lean_object* v___y_269_ = stack[3].m_obj;
lean_object* v___y_270_ = stack[4].m_obj;
lean_object* v___y_271_ = stack[5].m_obj;
lean_object* v___y_272_ = stack[6].m_obj;
lean_object* v_res_290_;
v_res_290_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_266_, v_a_267_, v_hidden_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___boxed(lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_hidden_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v_hidden_boxed_299_; lean_object* v_res_300_; 
v_hidden_boxed_299_ = lean_unbox(v_hidden_293_);
v_res_300_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_291_, v_a_292_, v_hidden_boxed_299_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_300_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__7));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__0);
v___x_304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__1);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__3);
v___x_307_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__1);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_309_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__3);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__4);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(lean_object* v_a_314_, lean_object* v_a_315_, size_t v___x_316_, size_t v___x_317_, lean_object* v_as_x27_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
if (lean_obj_tag(v_as_x27_318_) == 0)
{
lean_object* v___x_325_; 
lean_dec_ref(v_a_315_);
lean_dec_ref(v_a_314_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_319_);
return v___x_325_;
}
else
{
lean_object* v_toCold_326_; lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v_currRecDepth_329_; lean_object* v_ref_330_; uint8_t v_suppressElabErrors_331_; uint8_t v_isRecordingDeps_332_; lean_object* v_fileName_333_; lean_object* v_fileMap_334_; lean_object* v_options_335_; lean_object* v_currNamespace_336_; lean_object* v_openDecls_337_; lean_object* v_initHeartbeats_338_; lean_object* v_maxHeartbeats_339_; lean_object* v_quotContext_340_; lean_object* v_currMacroScope_341_; lean_object* v_cancelTk_x3f_342_; lean_object* v_inheritedTraceOptions_343_; lean_object* v___x_344_; lean_object* v___y_346_; uint16_t v___y_347_; lean_object* v_fileName_348_; lean_object* v_fileMap_349_; lean_object* v_currNamespace_350_; lean_object* v_openDecls_351_; lean_object* v_initHeartbeats_352_; lean_object* v_maxHeartbeats_353_; lean_object* v_quotContext_354_; lean_object* v_currMacroScope_355_; lean_object* v_cancelTk_x3f_356_; lean_object* v_inheritedTraceOptions_357_; lean_object* v_currRecDepth_358_; lean_object* v_ref_359_; uint8_t v_suppressElabErrors_360_; uint8_t v_isRecordingDeps_361_; lean_object* v___y_362_; uint8_t v___y_402_; lean_object* v___y_403_; uint16_t v___y_404_; uint8_t v___y_427_; lean_object* v___y_428_; uint16_t v___y_429_; uint8_t v___y_430_; uint8_t v___x_431_; lean_object* v___y_433_; 
v_toCold_326_ = lean_ctor_get(v___y_322_, 0);
v_head_327_ = lean_ctor_get(v_as_x27_318_, 0);
v_tail_328_ = lean_ctor_get(v_as_x27_318_, 1);
v_currRecDepth_329_ = lean_ctor_get(v___y_322_, 1);
v_ref_330_ = lean_ctor_get(v___y_322_, 2);
v_suppressElabErrors_331_ = lean_ctor_get_uint8(v___y_322_, sizeof(void*)*3 + 2);
v_isRecordingDeps_332_ = lean_ctor_get_uint8(v___y_322_, sizeof(void*)*3 + 3);
v_fileName_333_ = lean_ctor_get(v_toCold_326_, 0);
v_fileMap_334_ = lean_ctor_get(v_toCold_326_, 1);
v_options_335_ = lean_ctor_get(v_toCold_326_, 2);
v_currNamespace_336_ = lean_ctor_get(v_toCold_326_, 4);
v_openDecls_337_ = lean_ctor_get(v_toCold_326_, 5);
v_initHeartbeats_338_ = lean_ctor_get(v_toCold_326_, 6);
v_maxHeartbeats_339_ = lean_ctor_get(v_toCold_326_, 7);
v_quotContext_340_ = lean_ctor_get(v_toCold_326_, 8);
v_currMacroScope_341_ = lean_ctor_get(v_toCold_326_, 9);
v_cancelTk_x3f_342_ = lean_ctor_get(v_toCold_326_, 10);
v_inheritedTraceOptions_343_ = lean_ctor_get(v_toCold_326_, 11);
v___x_344_ = lean_box(0);
v___x_431_ = lean_usize_dec_eq(v___x_316_, v___x_317_);
if (v_isRecordingDeps_332_ == 0)
{
lean_object* v___x_443_; 
lean_inc(v_head_327_);
lean_inc_ref(v_options_335_);
v___x_443_ = lean_apply_1(v_head_327_, v_options_335_);
v___y_433_ = v___x_443_;
goto v___jp_432_;
}
else
{
lean_object* v___x_444_; 
lean_inc_ref(v_options_335_);
v___x_444_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_335_);
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
v___jp_345_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_363_ = l_Lean_maxRecDepth;
v___x_364_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_346_, v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_365_, 0, v_fileName_348_);
lean_ctor_set(v___x_365_, 1, v_fileMap_349_);
lean_ctor_set(v___x_365_, 2, v___y_346_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
lean_ctor_set(v___x_365_, 4, v_currNamespace_350_);
lean_ctor_set(v___x_365_, 5, v_openDecls_351_);
lean_ctor_set(v___x_365_, 6, v_initHeartbeats_352_);
lean_ctor_set(v___x_365_, 7, v_maxHeartbeats_353_);
lean_ctor_set(v___x_365_, 8, v_quotContext_354_);
lean_ctor_set(v___x_365_, 9, v_currMacroScope_355_);
lean_ctor_set(v___x_365_, 10, v_cancelTk_x3f_356_);
lean_ctor_set(v___x_365_, 11, v_inheritedTraceOptions_357_);
lean_inc(v_ref_359_);
lean_inc(v_currRecDepth_358_);
v___x_366_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_currRecDepth_358_);
lean_ctor_set(v___x_366_, 2, v_ref_359_);
lean_ctor_set_uint16(v___x_366_, sizeof(void*)*3, v___y_347_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*3 + 2, v_suppressElabErrors_360_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*3 + 3, v_isRecordingDeps_361_);
lean_inc_ref(v_a_314_);
v___x_367_ = l_Lean_Meta_ppExpr(v_a_314_, v___y_320_, v___y_321_, v___x_366_, v___y_362_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
lean_inc_ref(v_a_315_);
v___x_369_ = l_Lean_Meta_ppExpr(v_a_315_, v___y_320_, v___y_321_, v___x_366_, v___y_362_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = l_Std_Format_defWidth;
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Std_Format_pretty(v_a_368_, v___x_371_, v___x_372_, v___x_372_);
v___x_374_ = l_Std_Format_pretty(v_a_370_, v___x_371_, v___x_372_, v___x_372_);
v___x_375_ = lean_string_dec_eq(v___x_373_, v___x_374_);
lean_dec_ref(v___x_374_);
lean_dec_ref(v___x_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_376_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_377_ = l_Lean_indentExpr(v_a_314_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_indentExpr(v_a_315_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_382_, v___y_320_, v___y_321_, v___x_366_, v___y_362_);
lean_dec_ref_known(v___x_366_, 3);
return v___x_383_;
}
else
{
lean_dec_ref_known(v___x_366_, 3);
v_as_x27_318_ = v_tail_328_;
v_b_319_ = v___x_344_;
goto _start;
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_368_);
lean_dec_ref_known(v___x_366_, 3);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_a_314_);
v_a_385_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_369_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_369_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref_known(v___x_366_, 3);
lean_dec_ref(v_a_315_);
lean_dec_ref(v_a_314_);
v_a_393_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_367_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_367_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
v___jp_401_:
{
lean_object* v___x_405_; lean_object* v_env_406_; lean_object* v_nextMacroScope_407_; lean_object* v_ngen_408_; lean_object* v_auxDeclNGen_409_; lean_object* v_traceState_410_; lean_object* v_recordedDeps_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_424_; 
v___x_405_ = lean_st_ref_take(v___y_323_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
v_nextMacroScope_407_ = lean_ctor_get(v___x_405_, 1);
v_ngen_408_ = lean_ctor_get(v___x_405_, 2);
v_auxDeclNGen_409_ = lean_ctor_get(v___x_405_, 3);
v_traceState_410_ = lean_ctor_get(v___x_405_, 4);
v_recordedDeps_411_ = lean_ctor_get(v___x_405_, 6);
v_messages_412_ = lean_ctor_get(v___x_405_, 7);
v_infoState_413_ = lean_ctor_get(v___x_405_, 8);
v_snapshotTasks_414_ = lean_ctor_get(v___x_405_, 9);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_405_, 5);
lean_dec(v_unused_425_);
v___x_416_ = v___x_405_;
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_messages_412_);
lean_inc(v_recordedDeps_411_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_409_);
lean_inc(v_ngen_408_);
lean_inc(v_nextMacroScope_407_);
lean_inc(v_env_406_);
lean_dec(v___x_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_418_ = l_Lean_Kernel_enableDiag(v_env_406_, v___y_402_);
v___x_419_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 5, v___x_419_);
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_nextMacroScope_407_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_ngen_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_auxDeclNGen_409_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_traceState_410_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v_recordedDeps_411_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_messages_412_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_snapshotTasks_414_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; 
v___x_422_ = lean_st_ref_put(v___y_323_, v___x_421_);
lean_inc_ref(v_inheritedTraceOptions_343_);
lean_inc(v_cancelTk_x3f_342_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_340_);
lean_inc(v_maxHeartbeats_339_);
lean_inc(v_initHeartbeats_338_);
lean_inc(v_openDecls_337_);
lean_inc(v_currNamespace_336_);
lean_inc_ref(v_fileMap_334_);
lean_inc_ref(v_fileName_333_);
v___y_346_ = v___y_403_;
v___y_347_ = v___y_404_;
v_fileName_348_ = v_fileName_333_;
v_fileMap_349_ = v_fileMap_334_;
v_currNamespace_350_ = v_currNamespace_336_;
v_openDecls_351_ = v_openDecls_337_;
v_initHeartbeats_352_ = v_initHeartbeats_338_;
v_maxHeartbeats_353_ = v_maxHeartbeats_339_;
v_quotContext_354_ = v_quotContext_340_;
v_currMacroScope_355_ = v_currMacroScope_341_;
v_cancelTk_x3f_356_ = v_cancelTk_x3f_342_;
v_inheritedTraceOptions_357_ = v_inheritedTraceOptions_343_;
v_currRecDepth_358_ = v_currRecDepth_329_;
v_ref_359_ = v_ref_330_;
v_suppressElabErrors_360_ = v_suppressElabErrors_331_;
v_isRecordingDeps_361_ = v_isRecordingDeps_332_;
v___y_362_ = v___y_323_;
goto v___jp_345_;
}
}
}
v___jp_426_:
{
if (v___y_427_ == 0)
{
v___y_402_ = v___y_430_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_429_;
goto v___jp_401_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_343_);
lean_inc(v_cancelTk_x3f_342_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_340_);
lean_inc(v_maxHeartbeats_339_);
lean_inc(v_initHeartbeats_338_);
lean_inc(v_openDecls_337_);
lean_inc(v_currNamespace_336_);
lean_inc_ref(v_fileMap_334_);
lean_inc_ref(v_fileName_333_);
v___y_346_ = v___y_428_;
v___y_347_ = v___y_429_;
v_fileName_348_ = v_fileName_333_;
v_fileMap_349_ = v_fileMap_334_;
v_currNamespace_350_ = v_currNamespace_336_;
v_openDecls_351_ = v_openDecls_337_;
v_initHeartbeats_352_ = v_initHeartbeats_338_;
v_maxHeartbeats_353_ = v_maxHeartbeats_339_;
v_quotContext_354_ = v_quotContext_340_;
v_currMacroScope_355_ = v_currMacroScope_341_;
v_cancelTk_x3f_356_ = v_cancelTk_x3f_342_;
v_inheritedTraceOptions_357_ = v_inheritedTraceOptions_343_;
v_currRecDepth_358_ = v_currRecDepth_329_;
v_ref_359_ = v_ref_330_;
v_suppressElabErrors_360_ = v_suppressElabErrors_331_;
v_isRecordingDeps_361_ = v_isRecordingDeps_332_;
v___y_362_ = v___y_323_;
goto v___jp_345_;
}
}
v___jp_432_:
{
uint16_t v___x_434_; lean_object* v___x_435_; lean_object* v_env_436_; uint8_t v___x_437_; uint16_t v___x_438_; uint16_t v___x_439_; uint16_t v___x_440_; uint8_t v___x_441_; 
v___x_434_ = l_Lean_OptionFlags_ofOptions(v___y_433_);
v___x_435_ = lean_st_ref_get(v___y_323_);
v_env_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_env_436_);
lean_dec(v___x_435_);
v___x_437_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_436_);
lean_dec_ref(v_env_436_);
v___x_438_ = 512;
v___x_439_ = lean_uint16_land(v___x_434_, v___x_438_);
v___x_440_ = 0;
v___x_441_ = lean_uint16_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 1;
v___y_427_ = v___x_437_;
v___y_428_ = v___y_433_;
v___y_429_ = v___x_434_;
v___y_430_ = v___x_442_;
goto v___jp_426_;
}
else
{
if (v___x_431_ == 0)
{
if (v___x_437_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_343_);
lean_inc(v_cancelTk_x3f_342_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_340_);
lean_inc(v_maxHeartbeats_339_);
lean_inc(v_initHeartbeats_338_);
lean_inc(v_openDecls_337_);
lean_inc(v_currNamespace_336_);
lean_inc_ref(v_fileMap_334_);
lean_inc_ref(v_fileName_333_);
v___y_346_ = v___y_433_;
v___y_347_ = v___x_434_;
v_fileName_348_ = v_fileName_333_;
v_fileMap_349_ = v_fileMap_334_;
v_currNamespace_350_ = v_currNamespace_336_;
v_openDecls_351_ = v_openDecls_337_;
v_initHeartbeats_352_ = v_initHeartbeats_338_;
v_maxHeartbeats_353_ = v_maxHeartbeats_339_;
v_quotContext_354_ = v_quotContext_340_;
v_currMacroScope_355_ = v_currMacroScope_341_;
v_cancelTk_x3f_356_ = v_cancelTk_x3f_342_;
v_inheritedTraceOptions_357_ = v_inheritedTraceOptions_343_;
v_currRecDepth_358_ = v_currRecDepth_329_;
v_ref_359_ = v_ref_330_;
v_suppressElabErrors_360_ = v_suppressElabErrors_331_;
v_isRecordingDeps_361_ = v_isRecordingDeps_332_;
v___y_362_ = v___y_323_;
goto v___jp_345_;
}
else
{
v___y_402_ = v___x_431_;
v___y_403_ = v___y_433_;
v___y_404_ = v___x_434_;
goto v___jp_401_;
}
}
else
{
v___y_427_ = v___x_437_;
v___y_428_ = v___y_433_;
v___y_429_ = v___x_434_;
v___y_430_ = v___x_431_;
goto v___jp_426_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_a_315_ = stack[1].m_obj;
size_t v___x_316_ = stack[2].m_num;
size_t v___x_317_ = stack[3].m_num;
lean_object* v_as_x27_318_ = stack[4].m_obj;
lean_object* v_b_319_ = stack[5].m_obj;
lean_object* v___y_320_ = stack[6].m_obj;
lean_object* v___y_321_ = stack[7].m_obj;
lean_object* v___y_322_ = stack[8].m_obj;
lean_object* v___y_323_ = stack[9].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_314_, v_a_315_, v___x_316_, v___x_317_, v_as_x27_318_, v_b_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___boxed(lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v_as_x27_450_, lean_object* v_b_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
size_t v___x_49600__boxed_457_; size_t v___x_49601__boxed_458_; lean_object* v_res_459_; 
v___x_49600__boxed_457_ = lean_unbox_usize(v___x_448_);
lean_dec(v___x_448_);
v___x_49601__boxed_458_ = lean_unbox_usize(v___x_449_);
lean_dec(v___x_449_);
v_res_459_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_446_, v_a_447_, v___x_49600__boxed_457_, v___x_49601__boxed_458_, v_as_x27_450_, v_b_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v_as_x27_450_);
return v_res_459_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(lean_object* v_a_460_, lean_object* v_a_461_, size_t v___x_462_, size_t v___x_463_, lean_object* v_as_464_, lean_object* v_as_x27_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
if (lean_obj_tag(v_as_x27_465_) == 0)
{
lean_object* v___x_477_; 
lean_dec_ref(v_a_461_);
lean_dec_ref(v_a_460_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_b_466_);
return v___x_477_;
}
else
{
lean_object* v_toCold_478_; lean_object* v_head_479_; lean_object* v_tail_480_; lean_object* v_currRecDepth_481_; lean_object* v_ref_482_; uint8_t v_suppressElabErrors_483_; uint8_t v_isRecordingDeps_484_; lean_object* v_fileName_485_; lean_object* v_fileMap_486_; lean_object* v_options_487_; lean_object* v_currNamespace_488_; lean_object* v_openDecls_489_; lean_object* v_initHeartbeats_490_; lean_object* v_maxHeartbeats_491_; lean_object* v_quotContext_492_; lean_object* v_currMacroScope_493_; lean_object* v_cancelTk_x3f_494_; lean_object* v_inheritedTraceOptions_495_; lean_object* v___x_496_; lean_object* v___y_498_; uint16_t v___y_499_; lean_object* v_fileName_500_; lean_object* v_fileMap_501_; lean_object* v_currNamespace_502_; lean_object* v_openDecls_503_; lean_object* v_initHeartbeats_504_; lean_object* v_maxHeartbeats_505_; lean_object* v_quotContext_506_; lean_object* v_currMacroScope_507_; lean_object* v_cancelTk_x3f_508_; lean_object* v_inheritedTraceOptions_509_; lean_object* v_currRecDepth_510_; lean_object* v_ref_511_; uint8_t v_suppressElabErrors_512_; uint8_t v_isRecordingDeps_513_; lean_object* v___y_514_; lean_object* v___y_554_; uint16_t v___y_555_; uint8_t v___y_556_; uint8_t v___y_579_; lean_object* v___y_580_; uint16_t v___y_581_; uint8_t v___y_582_; uint8_t v___x_583_; lean_object* v___y_585_; 
v_toCold_478_ = lean_ctor_get(v___y_474_, 0);
v_head_479_ = lean_ctor_get(v_as_x27_465_, 0);
v_tail_480_ = lean_ctor_get(v_as_x27_465_, 1);
v_currRecDepth_481_ = lean_ctor_get(v___y_474_, 1);
v_ref_482_ = lean_ctor_get(v___y_474_, 2);
v_suppressElabErrors_483_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*3 + 2);
v_isRecordingDeps_484_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*3 + 3);
v_fileName_485_ = lean_ctor_get(v_toCold_478_, 0);
v_fileMap_486_ = lean_ctor_get(v_toCold_478_, 1);
v_options_487_ = lean_ctor_get(v_toCold_478_, 2);
v_currNamespace_488_ = lean_ctor_get(v_toCold_478_, 4);
v_openDecls_489_ = lean_ctor_get(v_toCold_478_, 5);
v_initHeartbeats_490_ = lean_ctor_get(v_toCold_478_, 6);
v_maxHeartbeats_491_ = lean_ctor_get(v_toCold_478_, 7);
v_quotContext_492_ = lean_ctor_get(v_toCold_478_, 8);
v_currMacroScope_493_ = lean_ctor_get(v_toCold_478_, 9);
v_cancelTk_x3f_494_ = lean_ctor_get(v_toCold_478_, 10);
v_inheritedTraceOptions_495_ = lean_ctor_get(v_toCold_478_, 11);
v___x_496_ = lean_box(0);
v___x_583_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
if (v_isRecordingDeps_484_ == 0)
{
lean_object* v___x_595_; 
lean_inc(v_head_479_);
lean_inc_ref(v_options_487_);
v___x_595_ = lean_apply_1(v_head_479_, v_options_487_);
v___y_585_ = v___x_595_;
goto v___jp_584_;
}
else
{
lean_object* v___x_596_; 
lean_inc_ref(v_options_487_);
v___x_596_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_487_);
v___y_585_ = v___x_596_;
goto v___jp_584_;
}
v___jp_497_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_515_ = l_Lean_maxRecDepth;
v___x_516_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_498_, v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_517_, 0, v_fileName_500_);
lean_ctor_set(v___x_517_, 1, v_fileMap_501_);
lean_ctor_set(v___x_517_, 2, v___y_498_);
lean_ctor_set(v___x_517_, 3, v___x_516_);
lean_ctor_set(v___x_517_, 4, v_currNamespace_502_);
lean_ctor_set(v___x_517_, 5, v_openDecls_503_);
lean_ctor_set(v___x_517_, 6, v_initHeartbeats_504_);
lean_ctor_set(v___x_517_, 7, v_maxHeartbeats_505_);
lean_ctor_set(v___x_517_, 8, v_quotContext_506_);
lean_ctor_set(v___x_517_, 9, v_currMacroScope_507_);
lean_ctor_set(v___x_517_, 10, v_cancelTk_x3f_508_);
lean_ctor_set(v___x_517_, 11, v_inheritedTraceOptions_509_);
lean_inc(v_ref_511_);
lean_inc(v_currRecDepth_510_);
v___x_518_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_currRecDepth_510_);
lean_ctor_set(v___x_518_, 2, v_ref_511_);
lean_ctor_set_uint16(v___x_518_, sizeof(void*)*3, v___y_499_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3 + 2, v_suppressElabErrors_512_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3 + 3, v_isRecordingDeps_513_);
lean_inc_ref(v_a_460_);
v___x_519_ = l_Lean_Meta_ppExpr(v_a_460_, v___y_472_, v___y_473_, v___x_518_, v___y_514_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
lean_inc_ref(v_a_461_);
v___x_521_ = l_Lean_Meta_ppExpr(v_a_461_, v___y_472_, v___y_473_, v___x_518_, v___y_514_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Std_Format_defWidth;
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Std_Format_pretty(v_a_520_, v___x_523_, v___x_524_, v___x_524_);
v___x_526_ = l_Std_Format_pretty(v_a_522_, v___x_523_, v___x_524_, v___x_524_);
v___x_527_ = lean_string_dec_eq(v___x_525_, v___x_526_);
lean_dec_ref(v___x_526_);
lean_dec_ref(v___x_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_528_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_529_ = l_Lean_indentExpr(v_a_460_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_indentExpr(v_a_461_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_534_, v___y_472_, v___y_473_, v___x_518_, v___y_514_);
lean_dec_ref_known(v___x_518_, 3);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
lean_dec_ref_known(v___x_518_, 3);
v___x_536_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_460_, v_a_461_, v___x_462_, v___x_463_, v_tail_480_, v___x_496_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_536_;
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_520_);
lean_dec_ref_known(v___x_518_, 3);
lean_dec_ref(v_a_461_);
lean_dec_ref(v_a_460_);
v_a_537_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_521_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_521_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
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
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref_known(v___x_518_, 3);
lean_dec_ref(v_a_461_);
lean_dec_ref(v_a_460_);
v_a_545_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_519_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_519_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
v___jp_553_:
{
lean_object* v___x_557_; lean_object* v_env_558_; lean_object* v_nextMacroScope_559_; lean_object* v_ngen_560_; lean_object* v_auxDeclNGen_561_; lean_object* v_traceState_562_; lean_object* v_recordedDeps_563_; lean_object* v_messages_564_; lean_object* v_infoState_565_; lean_object* v_snapshotTasks_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_576_; 
v___x_557_ = lean_st_ref_take(v___y_475_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
v_nextMacroScope_559_ = lean_ctor_get(v___x_557_, 1);
v_ngen_560_ = lean_ctor_get(v___x_557_, 2);
v_auxDeclNGen_561_ = lean_ctor_get(v___x_557_, 3);
v_traceState_562_ = lean_ctor_get(v___x_557_, 4);
v_recordedDeps_563_ = lean_ctor_get(v___x_557_, 6);
v_messages_564_ = lean_ctor_get(v___x_557_, 7);
v_infoState_565_ = lean_ctor_get(v___x_557_, 8);
v_snapshotTasks_566_ = lean_ctor_get(v___x_557_, 9);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v___x_557_, 5);
lean_dec(v_unused_577_);
v___x_568_ = v___x_557_;
v_isShared_569_ = v_isSharedCheck_576_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snapshotTasks_566_);
lean_inc(v_infoState_565_);
lean_inc(v_messages_564_);
lean_inc(v_recordedDeps_563_);
lean_inc(v_traceState_562_);
lean_inc(v_auxDeclNGen_561_);
lean_inc(v_ngen_560_);
lean_inc(v_nextMacroScope_559_);
lean_inc(v_env_558_);
lean_dec(v___x_557_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_576_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_570_ = l_Lean_Kernel_enableDiag(v_env_558_, v___y_556_);
v___x_571_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 5, v___x_571_);
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_573_ = v___x_568_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_nextMacroScope_559_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_ngen_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_auxDeclNGen_561_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_traceState_562_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_recordedDeps_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_messages_564_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_infoState_565_);
lean_ctor_set(v_reuseFailAlloc_575_, 9, v_snapshotTasks_566_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_st_ref_put(v___y_475_, v___x_573_);
lean_inc_ref(v_inheritedTraceOptions_495_);
lean_inc(v_cancelTk_x3f_494_);
lean_inc(v_currMacroScope_493_);
lean_inc(v_quotContext_492_);
lean_inc(v_maxHeartbeats_491_);
lean_inc(v_initHeartbeats_490_);
lean_inc(v_openDecls_489_);
lean_inc(v_currNamespace_488_);
lean_inc_ref(v_fileMap_486_);
lean_inc_ref(v_fileName_485_);
v___y_498_ = v___y_554_;
v___y_499_ = v___y_555_;
v_fileName_500_ = v_fileName_485_;
v_fileMap_501_ = v_fileMap_486_;
v_currNamespace_502_ = v_currNamespace_488_;
v_openDecls_503_ = v_openDecls_489_;
v_initHeartbeats_504_ = v_initHeartbeats_490_;
v_maxHeartbeats_505_ = v_maxHeartbeats_491_;
v_quotContext_506_ = v_quotContext_492_;
v_currMacroScope_507_ = v_currMacroScope_493_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_494_;
v_inheritedTraceOptions_509_ = v_inheritedTraceOptions_495_;
v_currRecDepth_510_ = v_currRecDepth_481_;
v_ref_511_ = v_ref_482_;
v_suppressElabErrors_512_ = v_suppressElabErrors_483_;
v_isRecordingDeps_513_ = v_isRecordingDeps_484_;
v___y_514_ = v___y_475_;
goto v___jp_497_;
}
}
}
v___jp_578_:
{
if (v___y_579_ == 0)
{
v___y_554_ = v___y_580_;
v___y_555_ = v___y_581_;
v___y_556_ = v___y_582_;
goto v___jp_553_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_495_);
lean_inc(v_cancelTk_x3f_494_);
lean_inc(v_currMacroScope_493_);
lean_inc(v_quotContext_492_);
lean_inc(v_maxHeartbeats_491_);
lean_inc(v_initHeartbeats_490_);
lean_inc(v_openDecls_489_);
lean_inc(v_currNamespace_488_);
lean_inc_ref(v_fileMap_486_);
lean_inc_ref(v_fileName_485_);
v___y_498_ = v___y_580_;
v___y_499_ = v___y_581_;
v_fileName_500_ = v_fileName_485_;
v_fileMap_501_ = v_fileMap_486_;
v_currNamespace_502_ = v_currNamespace_488_;
v_openDecls_503_ = v_openDecls_489_;
v_initHeartbeats_504_ = v_initHeartbeats_490_;
v_maxHeartbeats_505_ = v_maxHeartbeats_491_;
v_quotContext_506_ = v_quotContext_492_;
v_currMacroScope_507_ = v_currMacroScope_493_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_494_;
v_inheritedTraceOptions_509_ = v_inheritedTraceOptions_495_;
v_currRecDepth_510_ = v_currRecDepth_481_;
v_ref_511_ = v_ref_482_;
v_suppressElabErrors_512_ = v_suppressElabErrors_483_;
v_isRecordingDeps_513_ = v_isRecordingDeps_484_;
v___y_514_ = v___y_475_;
goto v___jp_497_;
}
}
v___jp_584_:
{
uint16_t v___x_586_; lean_object* v___x_587_; lean_object* v_env_588_; uint8_t v___x_589_; uint16_t v___x_590_; uint16_t v___x_591_; uint16_t v___x_592_; uint8_t v___x_593_; 
v___x_586_ = l_Lean_OptionFlags_ofOptions(v___y_585_);
v___x_587_ = lean_st_ref_get(v___y_475_);
v_env_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_588_);
lean_dec_ref(v_env_588_);
v___x_590_ = 512;
v___x_591_ = lean_uint16_land(v___x_586_, v___x_590_);
v___x_592_ = 0;
v___x_593_ = lean_uint16_dec_eq(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; 
v___x_594_ = 1;
v___y_579_ = v___x_589_;
v___y_580_ = v___y_585_;
v___y_581_ = v___x_586_;
v___y_582_ = v___x_594_;
goto v___jp_578_;
}
else
{
if (v___x_583_ == 0)
{
if (v___x_589_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_495_);
lean_inc(v_cancelTk_x3f_494_);
lean_inc(v_currMacroScope_493_);
lean_inc(v_quotContext_492_);
lean_inc(v_maxHeartbeats_491_);
lean_inc(v_initHeartbeats_490_);
lean_inc(v_openDecls_489_);
lean_inc(v_currNamespace_488_);
lean_inc_ref(v_fileMap_486_);
lean_inc_ref(v_fileName_485_);
v___y_498_ = v___y_585_;
v___y_499_ = v___x_586_;
v_fileName_500_ = v_fileName_485_;
v_fileMap_501_ = v_fileMap_486_;
v_currNamespace_502_ = v_currNamespace_488_;
v_openDecls_503_ = v_openDecls_489_;
v_initHeartbeats_504_ = v_initHeartbeats_490_;
v_maxHeartbeats_505_ = v_maxHeartbeats_491_;
v_quotContext_506_ = v_quotContext_492_;
v_currMacroScope_507_ = v_currMacroScope_493_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_494_;
v_inheritedTraceOptions_509_ = v_inheritedTraceOptions_495_;
v_currRecDepth_510_ = v_currRecDepth_481_;
v_ref_511_ = v_ref_482_;
v_suppressElabErrors_512_ = v_suppressElabErrors_483_;
v_isRecordingDeps_513_ = v_isRecordingDeps_484_;
v___y_514_ = v___y_475_;
goto v___jp_497_;
}
else
{
v___y_554_ = v___y_585_;
v___y_555_ = v___x_586_;
v___y_556_ = v___x_583_;
goto v___jp_553_;
}
}
else
{
v___y_579_ = v___x_589_;
v___y_580_ = v___y_585_;
v___y_581_ = v___x_586_;
v___y_582_ = v___x_583_;
goto v___jp_578_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[0].m_obj;
lean_object* v_a_461_ = stack[1].m_obj;
size_t v___x_462_ = stack[2].m_num;
size_t v___x_463_ = stack[3].m_num;
lean_object* v_as_464_ = stack[4].m_obj;
lean_object* v_as_x27_465_ = stack[5].m_obj;
lean_object* v_b_466_ = stack[6].m_obj;
lean_object* v___y_467_ = stack[7].m_obj;
lean_object* v___y_468_ = stack[8].m_obj;
lean_object* v___y_469_ = stack[9].m_obj;
lean_object* v___y_470_ = stack[10].m_obj;
lean_object* v___y_471_ = stack[11].m_obj;
lean_object* v___y_472_ = stack[12].m_obj;
lean_object* v___y_473_ = stack[13].m_obj;
lean_object* v___y_474_ = stack[14].m_obj;
lean_object* v___y_475_ = stack[15].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_460_, v_a_461_, v___x_462_, v___x_463_, v_as_464_, v_as_x27_465_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_a_598_ = _args[0];
lean_object* v_a_599_ = _args[1];
lean_object* v___x_600_ = _args[2];
lean_object* v___x_601_ = _args[3];
lean_object* v_as_602_ = _args[4];
lean_object* v_as_x27_603_ = _args[5];
lean_object* v_b_604_ = _args[6];
lean_object* v___y_605_ = _args[7];
lean_object* v___y_606_ = _args[8];
lean_object* v___y_607_ = _args[9];
lean_object* v___y_608_ = _args[10];
lean_object* v___y_609_ = _args[11];
lean_object* v___y_610_ = _args[12];
lean_object* v___y_611_ = _args[13];
lean_object* v___y_612_ = _args[14];
lean_object* v___y_613_ = _args[15];
lean_object* v___y_614_ = _args[16];
_start:
{
size_t v___x_49937__boxed_615_; size_t v___x_49938__boxed_616_; lean_object* v_res_617_; 
v___x_49937__boxed_615_ = lean_unbox_usize(v___x_600_);
lean_dec(v___x_600_);
v___x_49938__boxed_616_ = lean_unbox_usize(v___x_601_);
lean_dec(v___x_601_);
v_res_617_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_598_, v_a_599_, v___x_49937__boxed_615_, v___x_49938__boxed_616_, v_as_602_, v_as_x27_603_, v_b_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v_as_x27_603_);
lean_dec(v_as_602_);
return v_res_617_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(uint8_t v___y_618_, lean_object* v_a_619_, lean_object* v___f_620_, lean_object* v___f_621_, lean_object* v___f_622_, uint8_t v___x_623_, uint8_t v___x_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
switch(v___y_618_)
{
case 0:
{
lean_object* v___x_635_; 
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v___x_635_ = l_Lean_Meta_Grind_normLegacy(v_a_619_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_635_;
}
case 1:
{
lean_object* v___x_636_; 
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v___x_636_ = l_Lean_Meta_Grind_normSym___redArg(v_a_619_, v___y_626_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_636_;
}
default: 
{
lean_object* v___x_637_; 
lean_inc_ref(v_a_619_);
v___x_637_ = l_Lean_Meta_Grind_normLegacy(v_a_619_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_Lean_Meta_Grind_normSym___redArg(v_a_619_, v___y_626_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_expr_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v_expr_641_ = lean_ctor_get(v_a_638_, 0);
lean_inc_ref(v_expr_641_);
v___x_642_ = l_Lean_Meta_Sym_shareCommon(v_expr_641_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_expr_644_; lean_object* v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v_expr_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_expr_644_);
lean_dec(v_a_640_);
v___x_645_ = l_Lean_Meta_Sym_shareCommon(v_expr_644_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_723_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_723_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_723_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_723_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
size_t v___x_650_; size_t v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_ptr_addr(v_a_643_);
v___x_651_ = lean_ptr_addr(v_a_646_);
v___x_652_ = lean_usize_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___x_686_; 
lean_del_object(v___x_648_);
lean_dec(v_a_638_);
lean_inc(v_a_643_);
v___x_686_ = l_Lean_Meta_ppExpr(v_a_643_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
lean_inc(v_a_646_);
v___x_688_ = l_Lean_Meta_ppExpr(v_a_646_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = l_Std_Format_defWidth;
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = l_Std_Format_pretty(v_a_687_, v___x_690_, v___x_691_, v___x_691_);
v___x_693_ = l_Std_Format_pretty(v_a_689_, v___x_690_, v___x_691_, v___x_691_);
v___x_694_ = lean_string_dec_eq(v___x_692_, v___x_693_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_692_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v___x_695_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_643_, v_a_646_, v___x_624_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
v___y_654_ = v___y_625_;
v___y_655_ = v___y_626_;
v___y_656_ = v___y_627_;
v___y_657_ = v___y_628_;
v___y_658_ = v___y_629_;
v___y_659_ = v___y_630_;
v___y_660_ = v___y_631_;
v___y_661_ = v___y_632_;
v___y_662_ = v___y_633_;
goto v___jp_653_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_a_687_);
lean_dec(v_a_646_);
lean_dec(v_a_643_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v_a_704_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_688_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_688_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_646_);
lean_dec(v_a_643_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v_a_712_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_686_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_686_);
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
v___jp_653_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v___f_620_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v___f_621_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v___f_622_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_box(0);
lean_inc(v_a_646_);
lean_inc(v_a_643_);
v___x_668_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_643_, v_a_646_, v___x_650_, v___x_651_, v___x_666_, v___x_666_, v___x_667_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec_ref_known(v___x_666_, 2);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref_known(v___x_668_, 1);
v___x_669_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_643_, v_a_646_, v___x_623_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_a_646_);
lean_dec(v_a_643_);
v_a_678_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_668_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_668_);
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
else
{
lean_object* v___x_721_; 
lean_dec(v_a_646_);
lean_dec(v_a_643_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_a_638_);
v___x_721_ = v___x_648_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_638_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_643_);
lean_dec(v_a_638_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v_a_724_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_645_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_645_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_640_);
lean_dec(v_a_638_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
v_a_732_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_642_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_642_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_dec(v_a_638_);
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
return v___x_639_;
}
}
else
{
lean_dec_ref(v___f_622_);
lean_dec_ref(v___f_621_);
lean_dec_ref(v___f_620_);
lean_dec_ref(v_a_619_);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_618_ = stack[0].m_num;
lean_object* v_a_619_ = stack[1].m_obj;
lean_object* v___f_620_ = stack[2].m_obj;
lean_object* v___f_621_ = stack[3].m_obj;
lean_object* v___f_622_ = stack[4].m_obj;
uint8_t v___x_623_ = stack[5].m_num;
uint8_t v___x_624_ = stack[6].m_num;
lean_object* v___y_625_ = stack[7].m_obj;
lean_object* v___y_626_ = stack[8].m_obj;
lean_object* v___y_627_ = stack[9].m_obj;
lean_object* v___y_628_ = stack[10].m_obj;
lean_object* v___y_629_ = stack[11].m_obj;
lean_object* v___y_630_ = stack[12].m_obj;
lean_object* v___y_631_ = stack[13].m_obj;
lean_object* v___y_632_ = stack[14].m_obj;
lean_object* v___y_633_ = stack[15].m_obj;
lean_object* v_res_740_;
v_res_740_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(v___y_618_, v_a_619_, v___f_620_, v___f_621_, v___f_622_, v___x_623_, v___x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed(lean_object** _args){
lean_object* v___y_741_ = _args[0];
lean_object* v_a_742_ = _args[1];
lean_object* v___f_743_ = _args[2];
lean_object* v___f_744_ = _args[3];
lean_object* v___f_745_ = _args[4];
lean_object* v___x_746_ = _args[5];
lean_object* v___x_747_ = _args[6];
lean_object* v___y_748_ = _args[7];
lean_object* v___y_749_ = _args[8];
lean_object* v___y_750_ = _args[9];
lean_object* v___y_751_ = _args[10];
lean_object* v___y_752_ = _args[11];
lean_object* v___y_753_ = _args[12];
lean_object* v___y_754_ = _args[13];
lean_object* v___y_755_ = _args[14];
lean_object* v___y_756_ = _args[15];
lean_object* v___y_757_ = _args[16];
_start:
{
uint8_t v___y_50257__boxed_758_; uint8_t v___x_50262__boxed_759_; uint8_t v___x_50263__boxed_760_; lean_object* v_res_761_; 
v___y_50257__boxed_758_ = lean_unbox(v___y_741_);
v___x_50262__boxed_759_ = lean_unbox(v___x_746_);
v___x_50263__boxed_760_ = lean_unbox(v___x_747_);
v_res_761_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(v___y_50257__boxed_758_, v_a_742_, v___f_743_, v___f_744_, v___f_745_, v___x_50262__boxed_759_, v___x_50263__boxed_760_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
return v_res_761_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___y_774_; lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_764_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; uint8_t v___y_786_; uint8_t v_reducible_805_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v_reducible_805_ = lean_ctor_get_uint8(v_a_784_, sizeof(void*)*14 + 32);
lean_dec(v_a_784_);
if (v_reducible_805_ == 0)
{
uint8_t v___x_806_; 
v___x_806_ = 1;
v___y_786_ = v___x_806_;
goto v___jp_785_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = 2;
v___y_786_ = v___x_807_;
goto v___jp_785_;
}
v___jp_785_:
{
lean_object* v___x_787_; uint8_t v_transparency_788_; uint8_t v___x_789_; 
v___x_787_ = l_Lean_Meta_Context_config(v___y_768_);
v_transparency_788_ = lean_ctor_get_uint8(v___x_787_, 9);
lean_dec_ref(v___x_787_);
v___x_789_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_788_, v___y_786_);
if (v___x_789_ == 0)
{
lean_object* v_keyedConfig_790_; uint8_t v_trackZetaDelta_791_; lean_object* v_zetaDeltaSet_792_; lean_object* v_lctx_793_; lean_object* v_localInstances_794_; lean_object* v_defEqCtx_x3f_795_; lean_object* v_synthPendingDepth_796_; lean_object* v_customCanUnfoldPredicate_x3f_797_; uint8_t v_univApprox_798_; uint8_t v_inTypeClassResolution_799_; uint8_t v_cacheInferType_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_keyedConfig_790_ = lean_ctor_get(v___y_768_, 0);
v_trackZetaDelta_791_ = lean_ctor_get_uint8(v___y_768_, sizeof(void*)*7);
v_zetaDeltaSet_792_ = lean_ctor_get(v___y_768_, 1);
v_lctx_793_ = lean_ctor_get(v___y_768_, 2);
v_localInstances_794_ = lean_ctor_get(v___y_768_, 3);
v_defEqCtx_x3f_795_ = lean_ctor_get(v___y_768_, 4);
v_synthPendingDepth_796_ = lean_ctor_get(v___y_768_, 5);
v_customCanUnfoldPredicate_x3f_797_ = lean_ctor_get(v___y_768_, 6);
v_univApprox_798_ = lean_ctor_get_uint8(v___y_768_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_799_ = lean_ctor_get_uint8(v___y_768_, sizeof(void*)*7 + 2);
v_cacheInferType_800_ = lean_ctor_get_uint8(v___y_768_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_790_);
v___x_801_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_786_, v_keyedConfig_790_);
lean_inc(v_customCanUnfoldPredicate_x3f_797_);
lean_inc(v_synthPendingDepth_796_);
lean_inc(v_defEqCtx_x3f_795_);
lean_inc_ref(v_localInstances_794_);
lean_inc_ref(v_lctx_793_);
lean_inc(v_zetaDeltaSet_792_);
v___x_802_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_zetaDeltaSet_792_);
lean_ctor_set(v___x_802_, 2, v_lctx_793_);
lean_ctor_set(v___x_802_, 3, v_localInstances_794_);
lean_ctor_set(v___x_802_, 4, v_defEqCtx_x3f_795_);
lean_ctor_set(v___x_802_, 5, v_synthPendingDepth_796_);
lean_ctor_set(v___x_802_, 6, v_customCanUnfoldPredicate_x3f_797_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*7, v_trackZetaDelta_791_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*7 + 1, v_univApprox_798_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*7 + 2, v_inTypeClassResolution_799_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*7 + 3, v_cacheInferType_800_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_769_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
v___x_803_ = lean_apply_10(v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___x_802_, v___y_769_, v___y_770_, v___y_771_, lean_box(0));
v___y_774_ = v___x_803_;
goto v___jp_773_;
}
else
{
lean_object* v___x_804_; 
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
v___x_804_ = lean_apply_10(v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, lean_box(0));
v___y_774_ = v___x_804_;
goto v___jp_773_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___y_762_);
v_a_808_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_783_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_783_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
return v___y_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___y_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___y_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___y_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___y_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_762_ = stack[0].m_obj;
lean_object* v___y_763_ = stack[1].m_obj;
lean_object* v___y_764_ = stack[2].m_obj;
lean_object* v___y_765_ = stack[3].m_obj;
lean_object* v___y_766_ = stack[4].m_obj;
lean_object* v___y_767_ = stack[5].m_obj;
lean_object* v___y_768_ = stack[6].m_obj;
lean_object* v___y_769_ = stack[7].m_obj;
lean_object* v___y_770_ = stack[8].m_obj;
lean_object* v___y_771_ = stack[9].m_obj;
lean_object* v_res_816_;
v_res_816_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed(lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
return v_res_828_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(lean_object* v___x_830_, lean_object* v___x_831_, uint8_t v___x_832_, lean_object* v___f_833_, lean_object* v___f_834_, lean_object* v___f_835_, uint8_t v___x_836_, lean_object* v_stx_837_, lean_object* v___x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Elab_Tactic_elabGrindConfig___redArg(v___x_830_, v___x_831_, v___x_832_, v___y_839_, v___y_841_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; uint8_t v___y_851_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_913_ = l_Lean_Syntax_getArg(v_stx_837_, v___x_838_);
v___x_914_ = l_Lean_Syntax_getOptional_x3f(v___x_913_);
lean_dec(v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
uint8_t v___x_915_; 
v___x_915_ = 0;
v___y_851_ = v___x_915_;
goto v___jp_850_;
}
else
{
lean_object* v_val_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_val_916_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_914_, 1);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l_Lean_Syntax_getArg(v_val_916_, v___x_917_);
lean_dec(v_val_916_);
v___x_919_ = l_Lean_Syntax_getAtomVal(v___x_918_);
lean_dec(v___x_918_);
v___x_920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0));
v___x_921_ = lean_string_dec_eq(v___x_919_, v___x_920_);
lean_dec_ref(v___x_919_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = 2;
v___y_851_ = v___x_922_;
goto v___jp_850_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = 1;
v___y_851_ = v___x_923_;
goto v___jp_850_;
}
}
v___jp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_840_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc_n(v_a_853_, 2);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_MVarId_getType(v_a_853_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___y_861_; lean_object* v___f_862_; lean_object* v___x_863_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_a_855_, v___y_844_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc_n(v_a_857_, 2);
lean_dec_ref(v___x_856_);
v___x_858_ = lean_box(v___y_851_);
v___x_859_ = lean_box(v___x_832_);
v___x_860_ = lean_box(v___x_836_);
v___y_861_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed), 17, 7);
lean_closure_set(v___y_861_, 0, v___x_858_);
lean_closure_set(v___y_861_, 1, v_a_857_);
lean_closure_set(v___y_861_, 2, v___f_833_);
lean_closure_set(v___y_861_, 3, v___f_834_);
lean_closure_set(v___y_861_, 4, v___f_835_);
lean_closure_set(v___y_861_, 5, v___x_859_);
lean_closure_set(v___y_861_, 6, v___x_860_);
v___f_862_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed), 11, 1);
lean_closure_set(v___f_862_, 0, v___y_861_);
v___x_863_ = l_Lean_Meta_Grind_mkDefaultParams(v_a_849_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_box(0);
v___x_866_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_862_, v_a_864_, v___x_865_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = l_Lean_Meta_applySimpResultToTarget(v_a_853_, v_a_857_, v_a_867_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v_a_857_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v_a_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_871_, v___y_840_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_868_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_857_);
lean_dec(v_a_853_);
v_a_881_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_866_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_866_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v___f_862_);
lean_dec(v_a_857_);
lean_dec(v_a_853_);
v_a_889_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_863_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_863_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_a_853_);
lean_dec(v_a_849_);
lean_dec_ref(v___f_835_);
lean_dec_ref(v___f_834_);
lean_dec_ref(v___f_833_);
v_a_897_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_854_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_854_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_849_);
lean_dec_ref(v___f_835_);
lean_dec_ref(v___f_834_);
lean_dec_ref(v___f_833_);
v_a_905_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_852_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_852_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___f_835_);
lean_dec_ref(v___f_834_);
lean_dec_ref(v___f_833_);
v_a_924_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_848_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_848_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_830_ = stack[0].m_obj;
lean_object* v___x_831_ = stack[1].m_obj;
uint8_t v___x_832_ = stack[2].m_num;
lean_object* v___f_833_ = stack[3].m_obj;
lean_object* v___f_834_ = stack[4].m_obj;
lean_object* v___f_835_ = stack[5].m_obj;
uint8_t v___x_836_ = stack[6].m_num;
lean_object* v_stx_837_ = stack[7].m_obj;
lean_object* v___x_838_ = stack[8].m_obj;
lean_object* v___y_839_ = stack[9].m_obj;
lean_object* v___y_840_ = stack[10].m_obj;
lean_object* v___y_841_ = stack[11].m_obj;
lean_object* v___y_842_ = stack[12].m_obj;
lean_object* v___y_843_ = stack[13].m_obj;
lean_object* v___y_844_ = stack[14].m_obj;
lean_object* v___y_845_ = stack[15].m_obj;
lean_object* v___y_846_ = stack[16].m_obj;
lean_object* v_res_932_;
v_res_932_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(v___x_830_, v___x_831_, v___x_832_, v___f_833_, v___f_834_, v___f_835_, v___x_836_, v_stx_837_, v___x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed(lean_object** _args){
lean_object* v___x_933_ = _args[0];
lean_object* v___x_934_ = _args[1];
lean_object* v___x_935_ = _args[2];
lean_object* v___f_936_ = _args[3];
lean_object* v___f_937_ = _args[4];
lean_object* v___f_938_ = _args[5];
lean_object* v___x_939_ = _args[6];
lean_object* v_stx_940_ = _args[7];
lean_object* v___x_941_ = _args[8];
lean_object* v___y_942_ = _args[9];
lean_object* v___y_943_ = _args[10];
lean_object* v___y_944_ = _args[11];
lean_object* v___y_945_ = _args[12];
lean_object* v___y_946_ = _args[13];
lean_object* v___y_947_ = _args[14];
lean_object* v___y_948_ = _args[15];
lean_object* v___y_949_ = _args[16];
lean_object* v___y_950_ = _args[17];
_start:
{
uint8_t v___x_50806__boxed_951_; uint8_t v___x_50810__boxed_952_; lean_object* v_res_953_; 
v___x_50806__boxed_951_ = lean_unbox(v___x_935_);
v___x_50810__boxed_952_ = lean_unbox(v___x_939_);
v_res_953_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(v___x_933_, v___x_934_, v___x_50806__boxed_951_, v___f_936_, v___f_937_, v___f_938_, v___x_50810__boxed_952_, v_stx_940_, v___x_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___x_941_);
lean_dec(v_stx_940_);
return v_res_953_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(lean_object* v_stx_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; uint8_t v___x_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = l_Lean_Syntax_getArg(v_stx_980_, v___x_990_);
v___x_992_ = 0;
v___x_993_ = 1;
v___f_994_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0));
v___f_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1));
v___f_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2));
v___x_997_ = lean_unsigned_to_nat(2u);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3));
v___x_999_ = lean_box(v___x_993_);
v___x_1000_ = lean_box(v___x_992_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed), 18, 9);
lean_closure_set(v___f_1001_, 0, v___x_991_);
lean_closure_set(v___f_1001_, 1, v___x_998_);
lean_closure_set(v___f_1001_, 2, v___x_999_);
lean_closure_set(v___f_1001_, 3, v___f_996_);
lean_closure_set(v___f_1001_, 4, v___f_995_);
lean_closure_set(v___f_1001_, 5, v___f_994_);
lean_closure_set(v___f_1001_, 6, v___x_1000_);
lean_closure_set(v___f_1001_, 7, v_stx_980_);
lean_closure_set(v___f_1001_, 8, v___x_997_);
v___x_1002_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1001_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1002_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_980_ = stack[0].m_obj;
lean_object* v_a_981_ = stack[1].m_obj;
lean_object* v_a_982_ = stack[2].m_obj;
lean_object* v_a_983_ = stack[3].m_obj;
lean_object* v_a_984_ = stack[4].m_obj;
lean_object* v_a_985_ = stack[5].m_obj;
lean_object* v_a_986_ = stack[6].m_obj;
lean_object* v_a_987_ = stack[7].m_obj;
lean_object* v_a_988_ = stack[8].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(v_stx_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed(lean_object* v_stx_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(v_stx_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v_res_1014_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(lean_object* v_00_u03b1_1015_, lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1016_ = stack[1].m_obj;
lean_object* v___y_1017_ = stack[2].m_obj;
lean_object* v___y_1018_ = stack[3].m_obj;
lean_object* v___y_1019_ = stack[4].m_obj;
lean_object* v___y_1020_ = stack[5].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(lean_box(0), v_msg_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(v_00_u03b1_1024_, v_msg_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1031_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(lean_object* v_a_1032_, lean_object* v_a_1033_, size_t v___x_1034_, size_t v___x_1035_, lean_object* v_as_1036_, lean_object* v_as_x27_1037_, lean_object* v_b_1038_, lean_object* v_a_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_1032_, v_a_1033_, v___x_1034_, v___x_1035_, v_as_1036_, v_as_x27_1037_, v_b_1038_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1032_ = stack[0].m_obj;
lean_object* v_a_1033_ = stack[1].m_obj;
size_t v___x_1034_ = stack[2].m_num;
size_t v___x_1035_ = stack[3].m_num;
lean_object* v_as_1036_ = stack[4].m_obj;
lean_object* v_as_x27_1037_ = stack[5].m_obj;
lean_object* v_b_1038_ = stack[6].m_obj;
lean_object* v___y_1040_ = stack[8].m_obj;
lean_object* v___y_1041_ = stack[9].m_obj;
lean_object* v___y_1042_ = stack[10].m_obj;
lean_object* v___y_1043_ = stack[11].m_obj;
lean_object* v___y_1044_ = stack[12].m_obj;
lean_object* v___y_1045_ = stack[13].m_obj;
lean_object* v___y_1046_ = stack[14].m_obj;
lean_object* v___y_1047_ = stack[15].m_obj;
lean_object* v___y_1048_ = stack[16].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(v_a_1032_, v_a_1033_, v___x_1034_, v___x_1035_, v_as_1036_, v_as_x27_1037_, v_b_1038_, lean_box(0), v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___boxed(lean_object** _args){
lean_object* v_a_1052_ = _args[0];
lean_object* v_a_1053_ = _args[1];
lean_object* v___x_1054_ = _args[2];
lean_object* v___x_1055_ = _args[3];
lean_object* v_as_1056_ = _args[4];
lean_object* v_as_x27_1057_ = _args[5];
lean_object* v_b_1058_ = _args[6];
lean_object* v_a_1059_ = _args[7];
lean_object* v___y_1060_ = _args[8];
lean_object* v___y_1061_ = _args[9];
lean_object* v___y_1062_ = _args[10];
lean_object* v___y_1063_ = _args[11];
lean_object* v___y_1064_ = _args[12];
lean_object* v___y_1065_ = _args[13];
lean_object* v___y_1066_ = _args[14];
lean_object* v___y_1067_ = _args[15];
lean_object* v___y_1068_ = _args[16];
lean_object* v___y_1069_ = _args[17];
_start:
{
size_t v___x_51386__boxed_1070_; size_t v___x_51387__boxed_1071_; lean_object* v_res_1072_; 
v___x_51386__boxed_1070_ = lean_unbox_usize(v___x_1054_);
lean_dec(v___x_1054_);
v___x_51387__boxed_1071_ = lean_unbox_usize(v___x_1055_);
lean_dec(v___x_1055_);
v_res_1072_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(v_a_1052_, v_a_1053_, v___x_51386__boxed_1070_, v___x_51387__boxed_1071_, v_as_1056_, v_as_x27_1057_, v_b_1058_, v_a_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v_as_x27_1057_);
lean_dec(v_as_1056_);
return v_res_1072_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(lean_object* v_a_1073_, lean_object* v_a_1074_, size_t v___x_1075_, size_t v___x_1076_, lean_object* v_as_1077_, lean_object* v_as_x27_1078_, lean_object* v_b_1079_, lean_object* v_a_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_1073_, v_a_1074_, v___x_1075_, v___x_1076_, v_as_x27_1078_, v_b_1079_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1073_ = stack[0].m_obj;
lean_object* v_a_1074_ = stack[1].m_obj;
size_t v___x_1075_ = stack[2].m_num;
size_t v___x_1076_ = stack[3].m_num;
lean_object* v_as_1077_ = stack[4].m_obj;
lean_object* v_as_x27_1078_ = stack[5].m_obj;
lean_object* v_b_1079_ = stack[6].m_obj;
lean_object* v___y_1081_ = stack[8].m_obj;
lean_object* v___y_1082_ = stack[9].m_obj;
lean_object* v___y_1083_ = stack[10].m_obj;
lean_object* v___y_1084_ = stack[11].m_obj;
lean_object* v___y_1085_ = stack[12].m_obj;
lean_object* v___y_1086_ = stack[13].m_obj;
lean_object* v___y_1087_ = stack[14].m_obj;
lean_object* v___y_1088_ = stack[15].m_obj;
lean_object* v___y_1089_ = stack[16].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(v_a_1073_, v_a_1074_, v___x_1075_, v___x_1076_, v_as_1077_, v_as_x27_1078_, v_b_1079_, lean_box(0), v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_a_1093_ = _args[0];
lean_object* v_a_1094_ = _args[1];
lean_object* v___x_1095_ = _args[2];
lean_object* v___x_1096_ = _args[3];
lean_object* v_as_1097_ = _args[4];
lean_object* v_as_x27_1098_ = _args[5];
lean_object* v_b_1099_ = _args[6];
lean_object* v_a_1100_ = _args[7];
lean_object* v___y_1101_ = _args[8];
lean_object* v___y_1102_ = _args[9];
lean_object* v___y_1103_ = _args[10];
lean_object* v___y_1104_ = _args[11];
lean_object* v___y_1105_ = _args[12];
lean_object* v___y_1106_ = _args[13];
lean_object* v___y_1107_ = _args[14];
lean_object* v___y_1108_ = _args[15];
lean_object* v___y_1109_ = _args[16];
lean_object* v___y_1110_ = _args[17];
_start:
{
size_t v___x_51464__boxed_1111_; size_t v___x_51465__boxed_1112_; lean_object* v_res_1113_; 
v___x_51464__boxed_1111_ = lean_unbox_usize(v___x_1095_);
lean_dec(v___x_1095_);
v___x_51465__boxed_1112_ = lean_unbox_usize(v___x_1096_);
lean_dec(v___x_1096_);
v_res_1113_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(v_a_1093_, v_a_1094_, v___x_51464__boxed_1111_, v___x_51465__boxed_1112_, v_as_1097_, v_as_x27_1098_, v_b_1099_, v_a_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v_as_x27_1098_);
lean_dec(v_as_1097_);
return v_res_1113_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1(){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4));
v___x_1164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20));
v___x_1165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed), 10, 0);
v___x_1166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1167_;
v_res_1167_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___boxed(lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
return v_res_1169_;
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

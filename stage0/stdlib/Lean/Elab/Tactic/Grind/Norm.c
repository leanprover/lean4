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
uint8_t v___x_49216__boxed_170_; uint8_t v___x_49217__boxed_171_; lean_object* v_res_172_; 
v___x_49216__boxed_170_ = lean_unbox(v___x_167_);
v___x_49217__boxed_171_ = lean_unbox(v___x_168_);
v_res_172_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__0(v___x_49216__boxed_170_, v___x_49217__boxed_171_, v_o_169_);
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
uint8_t v___x_49230__boxed_179_; lean_object* v_res_180_; 
v___x_49230__boxed_179_ = lean_unbox(v___x_177_);
v_res_180_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__1(v___x_49230__boxed_179_, v_x_178_);
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
uint8_t v___x_49240__boxed_190_; lean_object* v_res_191_; 
v___x_49240__boxed_190_ = lean_unbox(v___x_187_);
v_res_191_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__2(v___x_49240__boxed_190_, v___f_188_, v_o_189_);
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
lean_object* v_toCold_311_; lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v_currRecDepth_314_; lean_object* v_ref_315_; uint8_t v_suppressElabErrors_316_; uint8_t v_isRecordingDeps_317_; lean_object* v_fileName_318_; lean_object* v_fileMap_319_; lean_object* v_options_320_; lean_object* v_currNamespace_321_; lean_object* v_openDecls_322_; lean_object* v_initHeartbeats_323_; lean_object* v_maxHeartbeats_324_; lean_object* v_quotContext_325_; lean_object* v_currMacroScope_326_; lean_object* v_cancelTk_x3f_327_; lean_object* v_inheritedTraceOptions_328_; lean_object* v___x_329_; lean_object* v___y_331_; uint16_t v___y_332_; lean_object* v_fileName_333_; lean_object* v_fileMap_334_; lean_object* v_currNamespace_335_; lean_object* v_openDecls_336_; lean_object* v_initHeartbeats_337_; lean_object* v_maxHeartbeats_338_; lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; lean_object* v_cancelTk_x3f_341_; lean_object* v_inheritedTraceOptions_342_; lean_object* v_currRecDepth_343_; lean_object* v_ref_344_; uint8_t v_suppressElabErrors_345_; uint8_t v_isRecordingDeps_346_; lean_object* v___y_347_; lean_object* v___y_387_; uint8_t v___y_388_; uint16_t v___y_389_; uint8_t v___y_412_; lean_object* v___y_413_; uint16_t v___y_414_; uint8_t v___y_415_; uint8_t v___x_416_; lean_object* v___y_418_; 
v_toCold_311_ = lean_ctor_get(v___y_307_, 0);
v_head_312_ = lean_ctor_get(v_as_x27_303_, 0);
v_tail_313_ = lean_ctor_get(v_as_x27_303_, 1);
v_currRecDepth_314_ = lean_ctor_get(v___y_307_, 1);
v_ref_315_ = lean_ctor_get(v___y_307_, 2);
v_suppressElabErrors_316_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 2);
v_isRecordingDeps_317_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 3);
v_fileName_318_ = lean_ctor_get(v_toCold_311_, 0);
v_fileMap_319_ = lean_ctor_get(v_toCold_311_, 1);
v_options_320_ = lean_ctor_get(v_toCold_311_, 2);
v_currNamespace_321_ = lean_ctor_get(v_toCold_311_, 4);
v_openDecls_322_ = lean_ctor_get(v_toCold_311_, 5);
v_initHeartbeats_323_ = lean_ctor_get(v_toCold_311_, 6);
v_maxHeartbeats_324_ = lean_ctor_get(v_toCold_311_, 7);
v_quotContext_325_ = lean_ctor_get(v_toCold_311_, 8);
v_currMacroScope_326_ = lean_ctor_get(v_toCold_311_, 9);
v_cancelTk_x3f_327_ = lean_ctor_get(v_toCold_311_, 10);
v_inheritedTraceOptions_328_ = lean_ctor_get(v_toCold_311_, 11);
v___x_329_ = lean_box(0);
v___x_416_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v_isRecordingDeps_317_ == 0)
{
lean_object* v___x_428_; 
lean_inc(v_head_312_);
lean_inc_ref(v_options_320_);
v___x_428_ = lean_apply_1(v_head_312_, v_options_320_);
v___y_418_ = v___x_428_;
goto v___jp_417_;
}
else
{
lean_object* v___x_429_; 
lean_inc_ref(v_options_320_);
v___x_429_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_320_);
v___y_418_ = v___x_429_;
goto v___jp_417_;
}
v___jp_330_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_348_ = l_Lean_maxRecDepth;
v___x_349_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_331_, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_350_, 0, v_fileName_333_);
lean_ctor_set(v___x_350_, 1, v_fileMap_334_);
lean_ctor_set(v___x_350_, 2, v___y_331_);
lean_ctor_set(v___x_350_, 3, v___x_349_);
lean_ctor_set(v___x_350_, 4, v_currNamespace_335_);
lean_ctor_set(v___x_350_, 5, v_openDecls_336_);
lean_ctor_set(v___x_350_, 6, v_initHeartbeats_337_);
lean_ctor_set(v___x_350_, 7, v_maxHeartbeats_338_);
lean_ctor_set(v___x_350_, 8, v_quotContext_339_);
lean_ctor_set(v___x_350_, 9, v_currMacroScope_340_);
lean_ctor_set(v___x_350_, 10, v_cancelTk_x3f_341_);
lean_ctor_set(v___x_350_, 11, v_inheritedTraceOptions_342_);
lean_inc(v_ref_344_);
lean_inc(v_currRecDepth_343_);
v___x_351_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_currRecDepth_343_);
lean_ctor_set(v___x_351_, 2, v_ref_344_);
lean_ctor_set_uint16(v___x_351_, sizeof(void*)*3, v___y_332_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 2, v_suppressElabErrors_345_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 3, v_isRecordingDeps_346_);
lean_inc_ref(v_a_299_);
v___x_352_ = l_Lean_Meta_ppExpr(v_a_299_, v___y_305_, v___y_306_, v___x_351_, v___y_347_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_354_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
lean_inc_ref(v_a_300_);
v___x_354_ = l_Lean_Meta_ppExpr(v_a_300_, v___y_305_, v___y_306_, v___x_351_, v___y_347_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = l_Std_Format_defWidth;
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l_Std_Format_pretty(v_a_353_, v___x_356_, v___x_357_, v___x_357_);
v___x_359_ = l_Std_Format_pretty(v_a_355_, v___x_356_, v___x_357_, v___x_357_);
v___x_360_ = lean_string_dec_eq(v___x_358_, v___x_359_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v___x_358_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_361_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_362_ = l_Lean_indentExpr(v_a_299_);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_indentExpr(v_a_300_);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_367_, v___y_305_, v___y_306_, v___x_351_, v___y_347_);
lean_dec_ref_known(v___x_351_, 3);
return v___x_368_;
}
else
{
lean_dec_ref_known(v___x_351_, 3);
v_as_x27_303_ = v_tail_313_;
v_b_304_ = v___x_329_;
goto _start;
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_a_353_);
lean_dec_ref_known(v___x_351_, 3);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
v_a_370_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_354_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_354_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec_ref_known(v___x_351_, 3);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
v_a_378_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_352_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_352_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_390_; lean_object* v_env_391_; lean_object* v_nextMacroScope_392_; lean_object* v_ngen_393_; lean_object* v_auxDeclNGen_394_; lean_object* v_traceState_395_; lean_object* v_recordedDeps_396_; lean_object* v_messages_397_; lean_object* v_infoState_398_; lean_object* v_snapshotTasks_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v___x_390_ = lean_st_ref_take(v___y_308_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
v_nextMacroScope_392_ = lean_ctor_get(v___x_390_, 1);
v_ngen_393_ = lean_ctor_get(v___x_390_, 2);
v_auxDeclNGen_394_ = lean_ctor_get(v___x_390_, 3);
v_traceState_395_ = lean_ctor_get(v___x_390_, 4);
v_recordedDeps_396_ = lean_ctor_get(v___x_390_, 6);
v_messages_397_ = lean_ctor_get(v___x_390_, 7);
v_infoState_398_ = lean_ctor_get(v___x_390_, 8);
v_snapshotTasks_399_ = lean_ctor_get(v___x_390_, 9);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_390_, 5);
lean_dec(v_unused_410_);
v___x_401_ = v___x_390_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_snapshotTasks_399_);
lean_inc(v_infoState_398_);
lean_inc(v_messages_397_);
lean_inc(v_recordedDeps_396_);
lean_inc(v_traceState_395_);
lean_inc(v_auxDeclNGen_394_);
lean_inc(v_ngen_393_);
lean_inc(v_nextMacroScope_392_);
lean_inc(v_env_391_);
lean_dec(v___x_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = l_Lean_Kernel_enableDiag(v_env_391_, v___y_388_);
v___x_404_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 5, v___x_404_);
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_traceState_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_recordedDeps_396_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_messages_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_infoState_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_snapshotTasks_399_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_st_ref_put(v___y_308_, v___x_406_);
lean_inc_ref(v_inheritedTraceOptions_328_);
lean_inc(v_cancelTk_x3f_327_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
lean_inc(v_maxHeartbeats_324_);
lean_inc(v_initHeartbeats_323_);
lean_inc(v_openDecls_322_);
lean_inc(v_currNamespace_321_);
lean_inc_ref(v_fileMap_319_);
lean_inc_ref(v_fileName_318_);
v___y_331_ = v___y_387_;
v___y_332_ = v___y_389_;
v_fileName_333_ = v_fileName_318_;
v_fileMap_334_ = v_fileMap_319_;
v_currNamespace_335_ = v_currNamespace_321_;
v_openDecls_336_ = v_openDecls_322_;
v_initHeartbeats_337_ = v_initHeartbeats_323_;
v_maxHeartbeats_338_ = v_maxHeartbeats_324_;
v_quotContext_339_ = v_quotContext_325_;
v_currMacroScope_340_ = v_currMacroScope_326_;
v_cancelTk_x3f_341_ = v_cancelTk_x3f_327_;
v_inheritedTraceOptions_342_ = v_inheritedTraceOptions_328_;
v_currRecDepth_343_ = v_currRecDepth_314_;
v_ref_344_ = v_ref_315_;
v_suppressElabErrors_345_ = v_suppressElabErrors_316_;
v_isRecordingDeps_346_ = v_isRecordingDeps_317_;
v___y_347_ = v___y_308_;
goto v___jp_330_;
}
}
}
v___jp_411_:
{
if (v___y_412_ == 0)
{
v___y_387_ = v___y_413_;
v___y_388_ = v___y_415_;
v___y_389_ = v___y_414_;
goto v___jp_386_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_328_);
lean_inc(v_cancelTk_x3f_327_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
lean_inc(v_maxHeartbeats_324_);
lean_inc(v_initHeartbeats_323_);
lean_inc(v_openDecls_322_);
lean_inc(v_currNamespace_321_);
lean_inc_ref(v_fileMap_319_);
lean_inc_ref(v_fileName_318_);
v___y_331_ = v___y_413_;
v___y_332_ = v___y_414_;
v_fileName_333_ = v_fileName_318_;
v_fileMap_334_ = v_fileMap_319_;
v_currNamespace_335_ = v_currNamespace_321_;
v_openDecls_336_ = v_openDecls_322_;
v_initHeartbeats_337_ = v_initHeartbeats_323_;
v_maxHeartbeats_338_ = v_maxHeartbeats_324_;
v_quotContext_339_ = v_quotContext_325_;
v_currMacroScope_340_ = v_currMacroScope_326_;
v_cancelTk_x3f_341_ = v_cancelTk_x3f_327_;
v_inheritedTraceOptions_342_ = v_inheritedTraceOptions_328_;
v_currRecDepth_343_ = v_currRecDepth_314_;
v_ref_344_ = v_ref_315_;
v_suppressElabErrors_345_ = v_suppressElabErrors_316_;
v_isRecordingDeps_346_ = v_isRecordingDeps_317_;
v___y_347_ = v___y_308_;
goto v___jp_330_;
}
}
v___jp_417_:
{
uint16_t v___x_419_; lean_object* v___x_420_; lean_object* v_env_421_; uint8_t v___x_422_; uint16_t v___x_423_; uint16_t v___x_424_; uint16_t v___x_425_; uint8_t v___x_426_; 
v___x_419_ = l_Lean_OptionFlags_ofOptions(v___y_418_);
v___x_420_ = lean_st_ref_get(v___y_308_);
v_env_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc_ref(v_env_421_);
lean_dec(v___x_420_);
v___x_422_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_421_);
lean_dec_ref(v_env_421_);
v___x_423_ = 512;
v___x_424_ = lean_uint16_land(v___x_419_, v___x_423_);
v___x_425_ = 0;
v___x_426_ = lean_uint16_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 1;
v___y_412_ = v___x_422_;
v___y_413_ = v___y_418_;
v___y_414_ = v___x_419_;
v___y_415_ = v___x_427_;
goto v___jp_411_;
}
else
{
if (v___x_416_ == 0)
{
if (v___x_422_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_328_);
lean_inc(v_cancelTk_x3f_327_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
lean_inc(v_maxHeartbeats_324_);
lean_inc(v_initHeartbeats_323_);
lean_inc(v_openDecls_322_);
lean_inc(v_currNamespace_321_);
lean_inc_ref(v_fileMap_319_);
lean_inc_ref(v_fileName_318_);
v___y_331_ = v___y_418_;
v___y_332_ = v___x_419_;
v_fileName_333_ = v_fileName_318_;
v_fileMap_334_ = v_fileMap_319_;
v_currNamespace_335_ = v_currNamespace_321_;
v_openDecls_336_ = v_openDecls_322_;
v_initHeartbeats_337_ = v_initHeartbeats_323_;
v_maxHeartbeats_338_ = v_maxHeartbeats_324_;
v_quotContext_339_ = v_quotContext_325_;
v_currMacroScope_340_ = v_currMacroScope_326_;
v_cancelTk_x3f_341_ = v_cancelTk_x3f_327_;
v_inheritedTraceOptions_342_ = v_inheritedTraceOptions_328_;
v_currRecDepth_343_ = v_currRecDepth_314_;
v_ref_344_ = v_ref_315_;
v_suppressElabErrors_345_ = v_suppressElabErrors_316_;
v_isRecordingDeps_346_ = v_isRecordingDeps_317_;
v___y_347_ = v___y_308_;
goto v___jp_330_;
}
else
{
v___y_387_ = v___y_418_;
v___y_388_ = v___x_416_;
v___y_389_ = v___x_419_;
goto v___jp_386_;
}
}
else
{
v___y_412_ = v___x_422_;
v___y_413_ = v___y_418_;
v___y_414_ = v___x_419_;
v___y_415_ = v___x_416_;
goto v___jp_411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___boxed(lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v_as_x27_434_, lean_object* v_b_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v___x_49441__boxed_441_; size_t v___x_49442__boxed_442_; lean_object* v_res_443_; 
v___x_49441__boxed_441_ = lean_unbox_usize(v___x_432_);
lean_dec(v___x_432_);
v___x_49442__boxed_442_ = lean_unbox_usize(v___x_433_);
lean_dec(v___x_433_);
v_res_443_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_430_, v_a_431_, v___x_49441__boxed_441_, v___x_49442__boxed_442_, v_as_x27_434_, v_b_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v_as_x27_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(lean_object* v_a_444_, lean_object* v_a_445_, size_t v___x_446_, size_t v___x_447_, lean_object* v_as_448_, lean_object* v_as_x27_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
if (lean_obj_tag(v_as_x27_449_) == 0)
{
lean_object* v___x_461_; 
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_b_450_);
return v___x_461_;
}
else
{
lean_object* v_toCold_462_; lean_object* v_head_463_; lean_object* v_tail_464_; lean_object* v_currRecDepth_465_; lean_object* v_ref_466_; uint8_t v_suppressElabErrors_467_; uint8_t v_isRecordingDeps_468_; lean_object* v_fileName_469_; lean_object* v_fileMap_470_; lean_object* v_options_471_; lean_object* v_currNamespace_472_; lean_object* v_openDecls_473_; lean_object* v_initHeartbeats_474_; lean_object* v_maxHeartbeats_475_; lean_object* v_quotContext_476_; lean_object* v_currMacroScope_477_; lean_object* v_cancelTk_x3f_478_; lean_object* v_inheritedTraceOptions_479_; lean_object* v___x_480_; uint16_t v___y_482_; lean_object* v___y_483_; lean_object* v_fileName_484_; lean_object* v_fileMap_485_; lean_object* v_currNamespace_486_; lean_object* v_openDecls_487_; lean_object* v_initHeartbeats_488_; lean_object* v_maxHeartbeats_489_; lean_object* v_quotContext_490_; lean_object* v_currMacroScope_491_; lean_object* v_cancelTk_x3f_492_; lean_object* v_inheritedTraceOptions_493_; lean_object* v_currRecDepth_494_; lean_object* v_ref_495_; uint8_t v_suppressElabErrors_496_; uint8_t v_isRecordingDeps_497_; lean_object* v___y_498_; uint16_t v___y_538_; lean_object* v___y_539_; uint8_t v___y_540_; uint16_t v___y_563_; uint8_t v___y_564_; lean_object* v___y_565_; uint8_t v___y_566_; uint8_t v___x_567_; lean_object* v___y_569_; 
v_toCold_462_ = lean_ctor_get(v___y_458_, 0);
v_head_463_ = lean_ctor_get(v_as_x27_449_, 0);
v_tail_464_ = lean_ctor_get(v_as_x27_449_, 1);
v_currRecDepth_465_ = lean_ctor_get(v___y_458_, 1);
v_ref_466_ = lean_ctor_get(v___y_458_, 2);
v_suppressElabErrors_467_ = lean_ctor_get_uint8(v___y_458_, sizeof(void*)*3 + 2);
v_isRecordingDeps_468_ = lean_ctor_get_uint8(v___y_458_, sizeof(void*)*3 + 3);
v_fileName_469_ = lean_ctor_get(v_toCold_462_, 0);
v_fileMap_470_ = lean_ctor_get(v_toCold_462_, 1);
v_options_471_ = lean_ctor_get(v_toCold_462_, 2);
v_currNamespace_472_ = lean_ctor_get(v_toCold_462_, 4);
v_openDecls_473_ = lean_ctor_get(v_toCold_462_, 5);
v_initHeartbeats_474_ = lean_ctor_get(v_toCold_462_, 6);
v_maxHeartbeats_475_ = lean_ctor_get(v_toCold_462_, 7);
v_quotContext_476_ = lean_ctor_get(v_toCold_462_, 8);
v_currMacroScope_477_ = lean_ctor_get(v_toCold_462_, 9);
v_cancelTk_x3f_478_ = lean_ctor_get(v_toCold_462_, 10);
v_inheritedTraceOptions_479_ = lean_ctor_get(v_toCold_462_, 11);
v___x_480_ = lean_box(0);
v___x_567_ = lean_usize_dec_eq(v___x_446_, v___x_447_);
if (v_isRecordingDeps_468_ == 0)
{
lean_object* v___x_579_; 
lean_inc(v_head_463_);
lean_inc_ref(v_options_471_);
v___x_579_ = lean_apply_1(v_head_463_, v_options_471_);
v___y_569_ = v___x_579_;
goto v___jp_568_;
}
else
{
lean_object* v___x_580_; 
lean_inc_ref(v_options_471_);
v___x_580_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_471_);
v___y_569_ = v___x_580_;
goto v___jp_568_;
}
v___jp_481_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_499_ = l_Lean_maxRecDepth;
v___x_500_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__3(v___y_483_, v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_501_, 0, v_fileName_484_);
lean_ctor_set(v___x_501_, 1, v_fileMap_485_);
lean_ctor_set(v___x_501_, 2, v___y_483_);
lean_ctor_set(v___x_501_, 3, v___x_500_);
lean_ctor_set(v___x_501_, 4, v_currNamespace_486_);
lean_ctor_set(v___x_501_, 5, v_openDecls_487_);
lean_ctor_set(v___x_501_, 6, v_initHeartbeats_488_);
lean_ctor_set(v___x_501_, 7, v_maxHeartbeats_489_);
lean_ctor_set(v___x_501_, 8, v_quotContext_490_);
lean_ctor_set(v___x_501_, 9, v_currMacroScope_491_);
lean_ctor_set(v___x_501_, 10, v_cancelTk_x3f_492_);
lean_ctor_set(v___x_501_, 11, v_inheritedTraceOptions_493_);
lean_inc(v_ref_495_);
lean_inc(v_currRecDepth_494_);
v___x_502_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v_currRecDepth_494_);
lean_ctor_set(v___x_502_, 2, v_ref_495_);
lean_ctor_set_uint16(v___x_502_, sizeof(void*)*3, v___y_482_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 2, v_suppressElabErrors_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3 + 3, v_isRecordingDeps_497_);
lean_inc_ref(v_a_444_);
v___x_503_ = l_Lean_Meta_ppExpr(v_a_444_, v___y_456_, v___y_457_, v___x_502_, v___y_498_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
lean_inc_ref(v_a_445_);
v___x_505_ = l_Lean_Meta_ppExpr(v_a_445_, v___y_456_, v___y_457_, v___x_502_, v___y_498_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_Std_Format_defWidth;
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Std_Format_pretty(v_a_504_, v___x_507_, v___x_508_, v___x_508_);
v___x_510_ = l_Std_Format_pretty(v_a_506_, v___x_507_, v___x_508_, v___x_508_);
v___x_511_ = lean_string_dec_eq(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
lean_dec_ref(v___x_509_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_512_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__2);
v___x_513_ = l_Lean_indentExpr(v_a_444_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5, &l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3___closed__5);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_indentExpr(v_a_445_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v___x_518_, v___y_456_, v___y_457_, v___x_502_, v___y_498_);
lean_dec_ref_known(v___x_502_, 3);
return v___x_519_;
}
else
{
lean_object* v___x_520_; 
lean_dec_ref_known(v___x_502_, 3);
v___x_520_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_444_, v_a_445_, v___x_446_, v___x_447_, v_tail_464_, v___x_480_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_520_;
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_a_504_);
lean_dec_ref_known(v___x_502_, 3);
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
v_a_521_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_505_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_505_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref_known(v___x_502_, 3);
lean_dec_ref(v_a_445_);
lean_dec_ref(v_a_444_);
v_a_529_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_503_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_503_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_541_; lean_object* v_env_542_; lean_object* v_nextMacroScope_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_traceState_546_; lean_object* v_recordedDeps_547_; lean_object* v_messages_548_; lean_object* v_infoState_549_; lean_object* v_snapshotTasks_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v___x_541_ = lean_st_ref_take(v___y_459_);
v_env_542_ = lean_ctor_get(v___x_541_, 0);
v_nextMacroScope_543_ = lean_ctor_get(v___x_541_, 1);
v_ngen_544_ = lean_ctor_get(v___x_541_, 2);
v_auxDeclNGen_545_ = lean_ctor_get(v___x_541_, 3);
v_traceState_546_ = lean_ctor_get(v___x_541_, 4);
v_recordedDeps_547_ = lean_ctor_get(v___x_541_, 6);
v_messages_548_ = lean_ctor_get(v___x_541_, 7);
v_infoState_549_ = lean_ctor_get(v___x_541_, 8);
v_snapshotTasks_550_ = lean_ctor_get(v___x_541_, 9);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v___x_541_, 5);
lean_dec(v_unused_561_);
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snapshotTasks_550_);
lean_inc(v_infoState_549_);
lean_inc(v_messages_548_);
lean_inc(v_recordedDeps_547_);
lean_inc(v_traceState_546_);
lean_inc(v_auxDeclNGen_545_);
lean_inc(v_ngen_544_);
lean_inc(v_nextMacroScope_543_);
lean_inc(v_env_542_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = l_Lean_Kernel_enableDiag(v_env_542_, v___y_540_);
v___x_555_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg___closed__5);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 5, v___x_555_);
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_nextMacroScope_543_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_ngen_544_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_auxDeclNGen_545_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_traceState_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 5, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 6, v_recordedDeps_547_);
lean_ctor_set(v_reuseFailAlloc_559_, 7, v_messages_548_);
lean_ctor_set(v_reuseFailAlloc_559_, 8, v_infoState_549_);
lean_ctor_set(v_reuseFailAlloc_559_, 9, v_snapshotTasks_550_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_st_ref_put(v___y_459_, v___x_557_);
lean_inc_ref(v_inheritedTraceOptions_479_);
lean_inc(v_cancelTk_x3f_478_);
lean_inc(v_currMacroScope_477_);
lean_inc(v_quotContext_476_);
lean_inc(v_maxHeartbeats_475_);
lean_inc(v_initHeartbeats_474_);
lean_inc(v_openDecls_473_);
lean_inc(v_currNamespace_472_);
lean_inc_ref(v_fileMap_470_);
lean_inc_ref(v_fileName_469_);
v___y_482_ = v___y_538_;
v___y_483_ = v___y_539_;
v_fileName_484_ = v_fileName_469_;
v_fileMap_485_ = v_fileMap_470_;
v_currNamespace_486_ = v_currNamespace_472_;
v_openDecls_487_ = v_openDecls_473_;
v_initHeartbeats_488_ = v_initHeartbeats_474_;
v_maxHeartbeats_489_ = v_maxHeartbeats_475_;
v_quotContext_490_ = v_quotContext_476_;
v_currMacroScope_491_ = v_currMacroScope_477_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_479_;
v_currRecDepth_494_ = v_currRecDepth_465_;
v_ref_495_ = v_ref_466_;
v_suppressElabErrors_496_ = v_suppressElabErrors_467_;
v_isRecordingDeps_497_ = v_isRecordingDeps_468_;
v___y_498_ = v___y_459_;
goto v___jp_481_;
}
}
}
v___jp_562_:
{
if (v___y_564_ == 0)
{
v___y_538_ = v___y_563_;
v___y_539_ = v___y_565_;
v___y_540_ = v___y_566_;
goto v___jp_537_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_479_);
lean_inc(v_cancelTk_x3f_478_);
lean_inc(v_currMacroScope_477_);
lean_inc(v_quotContext_476_);
lean_inc(v_maxHeartbeats_475_);
lean_inc(v_initHeartbeats_474_);
lean_inc(v_openDecls_473_);
lean_inc(v_currNamespace_472_);
lean_inc_ref(v_fileMap_470_);
lean_inc_ref(v_fileName_469_);
v___y_482_ = v___y_563_;
v___y_483_ = v___y_565_;
v_fileName_484_ = v_fileName_469_;
v_fileMap_485_ = v_fileMap_470_;
v_currNamespace_486_ = v_currNamespace_472_;
v_openDecls_487_ = v_openDecls_473_;
v_initHeartbeats_488_ = v_initHeartbeats_474_;
v_maxHeartbeats_489_ = v_maxHeartbeats_475_;
v_quotContext_490_ = v_quotContext_476_;
v_currMacroScope_491_ = v_currMacroScope_477_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_479_;
v_currRecDepth_494_ = v_currRecDepth_465_;
v_ref_495_ = v_ref_466_;
v_suppressElabErrors_496_ = v_suppressElabErrors_467_;
v_isRecordingDeps_497_ = v_isRecordingDeps_468_;
v___y_498_ = v___y_459_;
goto v___jp_481_;
}
}
v___jp_568_:
{
uint16_t v___x_570_; lean_object* v___x_571_; lean_object* v_env_572_; uint8_t v___x_573_; uint16_t v___x_574_; uint16_t v___x_575_; uint16_t v___x_576_; uint8_t v___x_577_; 
v___x_570_ = l_Lean_OptionFlags_ofOptions(v___y_569_);
v___x_571_ = lean_st_ref_get(v___y_459_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v___x_573_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_572_);
lean_dec_ref(v_env_572_);
v___x_574_ = 512;
v___x_575_ = lean_uint16_land(v___x_570_, v___x_574_);
v___x_576_ = 0;
v___x_577_ = lean_uint16_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; 
v___x_578_ = 1;
v___y_563_ = v___x_570_;
v___y_564_ = v___x_573_;
v___y_565_ = v___y_569_;
v___y_566_ = v___x_578_;
goto v___jp_562_;
}
else
{
if (v___x_567_ == 0)
{
if (v___x_573_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_479_);
lean_inc(v_cancelTk_x3f_478_);
lean_inc(v_currMacroScope_477_);
lean_inc(v_quotContext_476_);
lean_inc(v_maxHeartbeats_475_);
lean_inc(v_initHeartbeats_474_);
lean_inc(v_openDecls_473_);
lean_inc(v_currNamespace_472_);
lean_inc_ref(v_fileMap_470_);
lean_inc_ref(v_fileName_469_);
v___y_482_ = v___x_570_;
v___y_483_ = v___y_569_;
v_fileName_484_ = v_fileName_469_;
v_fileMap_485_ = v_fileMap_470_;
v_currNamespace_486_ = v_currNamespace_472_;
v_openDecls_487_ = v_openDecls_473_;
v_initHeartbeats_488_ = v_initHeartbeats_474_;
v_maxHeartbeats_489_ = v_maxHeartbeats_475_;
v_quotContext_490_ = v_quotContext_476_;
v_currMacroScope_491_ = v_currMacroScope_477_;
v_cancelTk_x3f_492_ = v_cancelTk_x3f_478_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_479_;
v_currRecDepth_494_ = v_currRecDepth_465_;
v_ref_495_ = v_ref_466_;
v_suppressElabErrors_496_ = v_suppressElabErrors_467_;
v_isRecordingDeps_497_ = v_isRecordingDeps_468_;
v___y_498_ = v___y_459_;
goto v___jp_481_;
}
else
{
v___y_538_ = v___x_570_;
v___y_539_ = v___y_569_;
v___y_540_ = v___x_567_;
goto v___jp_537_;
}
}
else
{
v___y_563_ = v___x_570_;
v___y_564_ = v___x_573_;
v___y_565_ = v___y_569_;
v___y_566_ = v___x_567_;
goto v___jp_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_a_581_ = _args[0];
lean_object* v_a_582_ = _args[1];
lean_object* v___x_583_ = _args[2];
lean_object* v___x_584_ = _args[3];
lean_object* v_as_585_ = _args[4];
lean_object* v_as_x27_586_ = _args[5];
lean_object* v_b_587_ = _args[6];
lean_object* v___y_588_ = _args[7];
lean_object* v___y_589_ = _args[8];
lean_object* v___y_590_ = _args[9];
lean_object* v___y_591_ = _args[10];
lean_object* v___y_592_ = _args[11];
lean_object* v___y_593_ = _args[12];
lean_object* v___y_594_ = _args[13];
lean_object* v___y_595_ = _args[14];
lean_object* v___y_596_ = _args[15];
lean_object* v___y_597_ = _args[16];
_start:
{
size_t v___x_49667__boxed_598_; size_t v___x_49668__boxed_599_; lean_object* v_res_600_; 
v___x_49667__boxed_598_ = lean_unbox_usize(v___x_583_);
lean_dec(v___x_583_);
v___x_49668__boxed_599_ = lean_unbox_usize(v___x_584_);
lean_dec(v___x_584_);
v_res_600_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_581_, v_a_582_, v___x_49667__boxed_598_, v___x_49668__boxed_599_, v_as_585_, v_as_x27_586_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v_as_x27_586_);
lean_dec(v_as_585_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(uint8_t v___y_601_, lean_object* v_a_602_, lean_object* v___f_603_, lean_object* v___f_604_, lean_object* v___f_605_, uint8_t v___x_606_, uint8_t v___x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
switch(v___y_601_)
{
case 0:
{
lean_object* v___x_618_; 
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v___x_618_ = l_Lean_Meta_Grind_normLegacy(v_a_602_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_618_;
}
case 1:
{
lean_object* v___x_619_; 
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v___x_619_ = l_Lean_Meta_Grind_normSym___redArg(v_a_602_, v___y_609_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_619_;
}
default: 
{
lean_object* v___x_620_; 
lean_inc_ref(v_a_602_);
v___x_620_ = l_Lean_Meta_Grind_normLegacy(v_a_602_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_Lean_Meta_Grind_normSym___redArg(v_a_602_, v___y_609_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_expr_624_; lean_object* v___x_625_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v_expr_624_ = lean_ctor_get(v_a_621_, 0);
lean_inc_ref(v_expr_624_);
v___x_625_ = l_Lean_Meta_Sym_shareCommon(v_expr_624_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_expr_627_; lean_object* v___x_628_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v_expr_627_ = lean_ctor_get(v_a_623_, 0);
lean_inc_ref(v_expr_627_);
lean_dec(v_a_623_);
v___x_628_ = l_Lean_Meta_Sym_shareCommon(v_expr_627_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_706_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_706_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_706_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_706_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_ptr_addr(v_a_626_);
v___x_634_ = lean_ptr_addr(v_a_629_);
v___x_635_ = lean_usize_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___x_669_; 
lean_del_object(v___x_631_);
lean_dec(v_a_621_);
lean_inc(v_a_626_);
v___x_669_ = l_Lean_Meta_ppExpr(v_a_626_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
lean_inc(v_a_629_);
v___x_671_ = l_Lean_Meta_ppExpr(v_a_629_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = l_Std_Format_defWidth;
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = l_Std_Format_pretty(v_a_670_, v___x_673_, v___x_674_, v___x_674_);
v___x_676_ = l_Std_Format_pretty(v_a_672_, v___x_673_, v___x_674_, v___x_674_);
v___x_677_ = lean_string_dec_eq(v___x_675_, v___x_676_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v___x_678_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_626_, v_a_629_, v___x_607_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
v___y_637_ = v___y_608_;
v___y_638_ = v___y_609_;
v___y_639_ = v___y_610_;
v___y_640_ = v___y_611_;
v___y_641_ = v___y_612_;
v___y_642_ = v___y_613_;
v___y_643_ = v___y_614_;
v___y_644_ = v___y_615_;
v___y_645_ = v___y_616_;
goto v___jp_636_;
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_a_670_);
lean_dec(v_a_629_);
lean_dec(v_a_626_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v_a_687_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_671_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_671_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_a_629_);
lean_dec(v_a_626_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v_a_695_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_669_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_669_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
v___jp_636_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v___f_603_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___f_604_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___f_605_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_box(0);
lean_inc(v_a_629_);
lean_inc(v_a_626_);
v___x_651_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_626_, v_a_629_, v___x_633_, v___x_634_, v___x_649_, v___x_649_, v___x_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref_known(v___x_649_, 2);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__3(v_a_626_, v_a_629_, v___x_606_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_629_);
lean_dec(v_a_626_);
v_a_661_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_651_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_651_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_a_629_);
lean_dec(v_a_626_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_a_621_);
v___x_704_ = v___x_631_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_621_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_626_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v_a_707_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_628_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_628_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_a_623_);
lean_dec(v_a_621_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
v_a_715_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_625_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_625_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_dec(v_a_621_);
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
return v___x_622_;
}
}
else
{
lean_dec_ref(v___f_605_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
lean_dec_ref(v_a_602_);
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed(lean_object** _args){
lean_object* v___y_723_ = _args[0];
lean_object* v_a_724_ = _args[1];
lean_object* v___f_725_ = _args[2];
lean_object* v___f_726_ = _args[3];
lean_object* v___f_727_ = _args[4];
lean_object* v___x_728_ = _args[5];
lean_object* v___x_729_ = _args[6];
lean_object* v___y_730_ = _args[7];
lean_object* v___y_731_ = _args[8];
lean_object* v___y_732_ = _args[9];
lean_object* v___y_733_ = _args[10];
lean_object* v___y_734_ = _args[11];
lean_object* v___y_735_ = _args[12];
lean_object* v___y_736_ = _args[13];
lean_object* v___y_737_ = _args[14];
lean_object* v___y_738_ = _args[15];
lean_object* v___y_739_ = _args[16];
_start:
{
uint8_t v___y_49879__boxed_740_; uint8_t v___x_49884__boxed_741_; uint8_t v___x_49885__boxed_742_; lean_object* v_res_743_; 
v___y_49879__boxed_740_ = lean_unbox(v___y_723_);
v___x_49884__boxed_741_ = lean_unbox(v___x_728_);
v___x_49885__boxed_742_ = lean_unbox(v___x_729_);
v_res_743_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4(v___y_49879__boxed_740_, v_a_724_, v___f_725_, v___f_726_, v___f_727_, v___x_49884__boxed_741_, v___x_49885__boxed_742_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___y_756_; lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_746_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; uint8_t v___y_768_; uint8_t v_reducible_787_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_reducible_787_ = lean_ctor_get_uint8(v_a_766_, sizeof(void*)*14 + 32);
lean_dec(v_a_766_);
if (v_reducible_787_ == 0)
{
uint8_t v___x_788_; 
v___x_788_ = 1;
v___y_768_ = v___x_788_;
goto v___jp_767_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = 2;
v___y_768_ = v___x_789_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; uint8_t v_transparency_770_; uint8_t v___x_771_; 
v___x_769_ = l_Lean_Meta_Context_config(v___y_750_);
v_transparency_770_ = lean_ctor_get_uint8(v___x_769_, 9);
lean_dec_ref(v___x_769_);
v___x_771_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_770_, v___y_768_);
if (v___x_771_ == 0)
{
lean_object* v_keyedConfig_772_; uint8_t v_trackZetaDelta_773_; lean_object* v_zetaDeltaSet_774_; lean_object* v_lctx_775_; lean_object* v_localInstances_776_; lean_object* v_defEqCtx_x3f_777_; lean_object* v_synthPendingDepth_778_; lean_object* v_customCanUnfoldPredicate_x3f_779_; uint8_t v_univApprox_780_; uint8_t v_inTypeClassResolution_781_; uint8_t v_cacheInferType_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_keyedConfig_772_ = lean_ctor_get(v___y_750_, 0);
v_trackZetaDelta_773_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*7);
v_zetaDeltaSet_774_ = lean_ctor_get(v___y_750_, 1);
v_lctx_775_ = lean_ctor_get(v___y_750_, 2);
v_localInstances_776_ = lean_ctor_get(v___y_750_, 3);
v_defEqCtx_x3f_777_ = lean_ctor_get(v___y_750_, 4);
v_synthPendingDepth_778_ = lean_ctor_get(v___y_750_, 5);
v_customCanUnfoldPredicate_x3f_779_ = lean_ctor_get(v___y_750_, 6);
v_univApprox_780_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_781_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*7 + 2);
v_cacheInferType_782_ = lean_ctor_get_uint8(v___y_750_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_772_);
v___x_783_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_768_, v_keyedConfig_772_);
lean_inc(v_customCanUnfoldPredicate_x3f_779_);
lean_inc(v_synthPendingDepth_778_);
lean_inc(v_defEqCtx_x3f_777_);
lean_inc_ref(v_localInstances_776_);
lean_inc_ref(v_lctx_775_);
lean_inc(v_zetaDeltaSet_774_);
v___x_784_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_zetaDeltaSet_774_);
lean_ctor_set(v___x_784_, 2, v_lctx_775_);
lean_ctor_set(v___x_784_, 3, v_localInstances_776_);
lean_ctor_set(v___x_784_, 4, v_defEqCtx_x3f_777_);
lean_ctor_set(v___x_784_, 5, v_synthPendingDepth_778_);
lean_ctor_set(v___x_784_, 6, v_customCanUnfoldPredicate_x3f_779_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*7, v_trackZetaDelta_773_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*7 + 1, v_univApprox_780_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*7 + 2, v_inTypeClassResolution_781_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*7 + 3, v_cacheInferType_782_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
v___x_785_ = lean_apply_10(v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___x_784_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
v___y_756_ = v___x_785_;
goto v___jp_755_;
}
else
{
lean_object* v___x_786_; 
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
v___x_786_ = lean_apply_10(v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
v___y_756_ = v___x_786_;
goto v___jp_755_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___y_744_);
v_a_790_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_765_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_765_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
v___jp_755_:
{
if (lean_obj_tag(v___y_756_) == 0)
{
return v___y_756_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_a_757_ = lean_ctor_get(v___y_756_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___y_756_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___y_756_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___y_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed(lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5(v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(lean_object* v___x_811_, lean_object* v___x_812_, uint8_t v___x_813_, lean_object* v___f_814_, lean_object* v___f_815_, lean_object* v___f_816_, uint8_t v___x_817_, lean_object* v_stx_818_, lean_object* v___x_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Elab_Tactic_elabGrindConfig___redArg(v___x_811_, v___x_812_, v___x_813_, v___y_820_, v___y_822_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; uint8_t v___y_832_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_894_ = l_Lean_Syntax_getArg(v_stx_818_, v___x_819_);
v___x_895_ = l_Lean_Syntax_getOptional_x3f(v___x_894_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
uint8_t v___x_896_; 
v___x_896_ = 0;
v___y_832_ = v___x_896_;
goto v___jp_831_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_val_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_895_, 1);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lean_Syntax_getArg(v_val_897_, v___x_898_);
lean_dec(v_val_897_);
v___x_900_ = l_Lean_Syntax_getAtomVal(v___x_899_);
lean_dec(v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___closed__0));
v___x_902_ = lean_string_dec_eq(v___x_900_, v___x_901_);
lean_dec_ref(v___x_900_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
v___x_903_ = 2;
v___y_832_ = v___x_903_;
goto v___jp_831_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = 1;
v___y_832_ = v___x_904_;
goto v___jp_831_;
}
}
v___jp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_821_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_n(v_a_834_, 2);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_MVarId_getType(v_a_834_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___y_842_; lean_object* v___f_843_; lean_object* v___x_844_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__1___redArg(v_a_836_, v___y_825_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_n(v_a_838_, 2);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_box(v___y_832_);
v___x_840_ = lean_box(v___x_813_);
v___x_841_ = lean_box(v___x_817_);
v___y_842_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__4___boxed), 17, 7);
lean_closure_set(v___y_842_, 0, v___x_839_);
lean_closure_set(v___y_842_, 1, v_a_838_);
lean_closure_set(v___y_842_, 2, v___f_814_);
lean_closure_set(v___y_842_, 3, v___f_815_);
lean_closure_set(v___y_842_, 4, v___f_816_);
lean_closure_set(v___y_842_, 5, v___x_840_);
lean_closure_set(v___y_842_, 6, v___x_841_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__5___boxed), 11, 1);
lean_closure_set(v___f_843_, 0, v___y_842_);
v___x_844_ = l_Lean_Meta_Grind_mkDefaultParams(v_a_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = lean_box(0);
v___x_847_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_843_, v_a_845_, v___x_846_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = l_Lean_Meta_applySimpResultToTarget(v_a_834_, v_a_838_, v_a_848_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v_a_838_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v_a_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_852_, v___y_821_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_853_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_849_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_849_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_838_);
lean_dec(v_a_834_);
v_a_862_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_847_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_847_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v___f_843_);
lean_dec(v_a_838_);
lean_dec(v_a_834_);
v_a_870_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_844_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_844_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_834_);
lean_dec(v_a_830_);
lean_dec_ref(v___f_816_);
lean_dec_ref(v___f_815_);
lean_dec_ref(v___f_814_);
v_a_878_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_835_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_835_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_830_);
lean_dec_ref(v___f_816_);
lean_dec_ref(v___f_815_);
lean_dec_ref(v___f_814_);
v_a_886_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_833_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_833_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___f_816_);
lean_dec_ref(v___f_815_);
lean_dec_ref(v___f_814_);
v_a_905_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_829_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_829_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed(lean_object** _args){
lean_object* v___x_913_ = _args[0];
lean_object* v___x_914_ = _args[1];
lean_object* v___x_915_ = _args[2];
lean_object* v___f_916_ = _args[3];
lean_object* v___f_917_ = _args[4];
lean_object* v___f_918_ = _args[5];
lean_object* v___x_919_ = _args[6];
lean_object* v_stx_920_ = _args[7];
lean_object* v___x_921_ = _args[8];
lean_object* v___y_922_ = _args[9];
lean_object* v___y_923_ = _args[10];
lean_object* v___y_924_ = _args[11];
lean_object* v___y_925_ = _args[12];
lean_object* v___y_926_ = _args[13];
lean_object* v___y_927_ = _args[14];
lean_object* v___y_928_ = _args[15];
lean_object* v___y_929_ = _args[16];
lean_object* v___y_930_ = _args[17];
_start:
{
uint8_t v___x_50239__boxed_931_; uint8_t v___x_50243__boxed_932_; lean_object* v_res_933_; 
v___x_50239__boxed_931_ = lean_unbox(v___x_915_);
v___x_50243__boxed_932_ = lean_unbox(v___x_919_);
v_res_933_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6(v___x_913_, v___x_914_, v___x_50239__boxed_931_, v___f_916_, v___f_917_, v___f_918_, v___x_50243__boxed_932_, v_stx_920_, v___x_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___x_921_);
lean_dec(v_stx_920_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(lean_object* v_stx_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = l_Lean_Syntax_getArg(v_stx_960_, v___x_970_);
v___x_972_ = 0;
v___x_973_ = 1;
v___f_974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__0));
v___f_975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__1));
v___f_976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__2));
v___x_977_ = lean_unsigned_to_nat(2u);
v___x_978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___closed__3));
v___x_979_ = lean_box(v___x_973_);
v___x_980_ = lean_box(v___x_972_);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___lam__6___boxed), 18, 9);
lean_closure_set(v___f_981_, 0, v___x_971_);
lean_closure_set(v___f_981_, 1, v___x_978_);
lean_closure_set(v___f_981_, 2, v___x_979_);
lean_closure_set(v___f_981_, 3, v___f_976_);
lean_closure_set(v___f_981_, 4, v___f_975_);
lean_closure_set(v___f_981_, 5, v___f_974_);
lean_closure_set(v___f_981_, 6, v___x_980_);
lean_closure_set(v___f_981_, 7, v_stx_960_);
lean_closure_set(v___f_981_, 8, v___x_977_);
v___x_982_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_981_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed(lean_object* v_stx_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm(v_stx_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(lean_object* v_00_u03b1_994_, lean_object* v_msg_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___redArg(v_msg_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__2(v_00_u03b1_1002_, v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(lean_object* v_a_1010_, lean_object* v_a_1011_, size_t v___x_1012_, size_t v___x_1013_, lean_object* v_as_1014_, lean_object* v_as_x27_1015_, lean_object* v_b_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___redArg(v_a_1010_, v_a_1011_, v___x_1012_, v___x_1013_, v_as_1014_, v_as_x27_1015_, v_b_1016_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4___boxed(lean_object** _args){
lean_object* v_a_1029_ = _args[0];
lean_object* v_a_1030_ = _args[1];
lean_object* v___x_1031_ = _args[2];
lean_object* v___x_1032_ = _args[3];
lean_object* v_as_1033_ = _args[4];
lean_object* v_as_x27_1034_ = _args[5];
lean_object* v_b_1035_ = _args[6];
lean_object* v_a_1036_ = _args[7];
lean_object* v___y_1037_ = _args[8];
lean_object* v___y_1038_ = _args[9];
lean_object* v___y_1039_ = _args[10];
lean_object* v___y_1040_ = _args[11];
lean_object* v___y_1041_ = _args[12];
lean_object* v___y_1042_ = _args[13];
lean_object* v___y_1043_ = _args[14];
lean_object* v___y_1044_ = _args[15];
lean_object* v___y_1045_ = _args[16];
lean_object* v___y_1046_ = _args[17];
_start:
{
size_t v___x_50648__boxed_1047_; size_t v___x_50649__boxed_1048_; lean_object* v_res_1049_; 
v___x_50648__boxed_1047_ = lean_unbox_usize(v___x_1031_);
lean_dec(v___x_1031_);
v___x_50649__boxed_1048_ = lean_unbox_usize(v___x_1032_);
lean_dec(v___x_1032_);
v_res_1049_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4(v_a_1029_, v_a_1030_, v___x_50648__boxed_1047_, v___x_50649__boxed_1048_, v_as_1033_, v_as_x27_1034_, v_b_1035_, v_a_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec(v_as_x27_1034_);
lean_dec(v_as_1033_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(lean_object* v_a_1050_, lean_object* v_a_1051_, size_t v___x_1052_, size_t v___x_1053_, lean_object* v_as_1054_, lean_object* v_as_x27_1055_, lean_object* v_b_1056_, lean_object* v_a_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___redArg(v_a_1050_, v_a_1051_, v___x_1052_, v___x_1053_, v_as_x27_1055_, v_b_1056_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_a_1069_ = _args[0];
lean_object* v_a_1070_ = _args[1];
lean_object* v___x_1071_ = _args[2];
lean_object* v___x_1072_ = _args[3];
lean_object* v_as_1073_ = _args[4];
lean_object* v_as_x27_1074_ = _args[5];
lean_object* v_b_1075_ = _args[6];
lean_object* v_a_1076_ = _args[7];
lean_object* v___y_1077_ = _args[8];
lean_object* v___y_1078_ = _args[9];
lean_object* v___y_1079_ = _args[10];
lean_object* v___y_1080_ = _args[11];
lean_object* v___y_1081_ = _args[12];
lean_object* v___y_1082_ = _args[13];
lean_object* v___y_1083_ = _args[14];
lean_object* v___y_1084_ = _args[15];
lean_object* v___y_1085_ = _args[16];
lean_object* v___y_1086_ = _args[17];
_start:
{
size_t v___x_50695__boxed_1087_; size_t v___x_50696__boxed_1088_; lean_object* v_res_1089_; 
v___x_50695__boxed_1087_ = lean_unbox_usize(v___x_1071_);
lean_dec(v___x_1071_);
v___x_50696__boxed_1088_ = lean_unbox_usize(v___x_1072_);
lean_dec(v___x_1072_);
v_res_1089_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm_spec__4_spec__6(v_a_1069_, v_a_1070_, v___x_50695__boxed_1087_, v___x_50696__boxed_1088_, v_as_1073_, v_as_x27_1074_, v_b_1075_, v_a_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v_as_x27_1074_);
lean_dec(v_as_1073_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1(){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__4));
v___x_1140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___closed__20));
v___x_1141_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___boxed), 10, 0);
v___x_1142_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1138_, v___x_1139_, v___x_1140_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1___boxed(lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm___regBuiltin___private_Lean_Elab_Tactic_Grind_Norm_0__Lean_Elab_Tactic_evalGrindNorm__1();
return v_res_1144_;
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

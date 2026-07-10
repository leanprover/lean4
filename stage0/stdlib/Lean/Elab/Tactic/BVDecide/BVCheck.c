// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVCheck
// Imports: public import Lean.Elab.Tactic.BVDecide.BVDecide public import Lean.Meta.Tactic.TryThis import Lean.Meta.Tactic.BVDecide.TacticContext import Lean.Meta.Tactic.BVDecide.Normalize
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "cannot compute parent directory of `"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 73, 220, 166, 46, 65, 124, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 110, 156, 2, 215, 50, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_box(1);
v___x_24_ = l_Lean_MessageData_ofFormat(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_29_ = l_Lean_MessageData_ofFormat(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_31_) == 0)
{
return v_x_30_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_55_; 
v_head_32_ = lean_ctor_get(v_x_31_, 0);
v_tail_33_ = lean_ctor_get(v_x_31_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_31_);
if (v_isSharedCheck_55_ == 0)
{
v___x_35_ = v_x_31_;
v_isShared_36_ = v_isSharedCheck_55_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_tail_33_);
lean_inc(v_head_32_);
lean_dec(v_x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_55_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v_before_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_53_; 
v_before_37_ = lean_ctor_get(v_head_32_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_head_32_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v_head_32_, 1);
lean_dec(v_unused_54_);
v___x_39_ = v_head_32_;
v_isShared_40_ = v_isSharedCheck_53_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_before_37_);
lean_dec(v_head_32_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_53_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 7);
lean_ctor_set(v___x_39_, 1, v___x_41_);
lean_ctor_set(v___x_39_, 0, v_x_30_);
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_x_30_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_52_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 7);
lean_ctor_set(v___x_35_, 1, v___x_44_);
lean_ctor_set(v___x_35_, 0, v___x_43_);
v___x_46_ = v___x_35_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_51_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = l_Lean_MessageData_ofSyntax(v_before_37_);
v___x_48_ = l_Lean_indentD(v___x_47_);
v___x_49_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_46_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v_x_30_ = v___x_49_;
v_x_31_ = v_tail_33_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_56_, lean_object* v_opt_57_){
_start:
{
lean_object* v_name_58_; lean_object* v_defValue_59_; lean_object* v_map_60_; lean_object* v___x_61_; 
v_name_58_ = lean_ctor_get(v_opt_57_, 0);
v_defValue_59_ = lean_ctor_get(v_opt_57_, 1);
v_map_60_ = lean_ctor_get(v_opts_56_, 0);
v___x_61_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_60_, v_name_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
uint8_t v___x_62_; 
v___x_62_ = lean_unbox(v_defValue_59_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; 
v_val_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___x_61_, 1);
if (lean_obj_tag(v_val_63_) == 1)
{
uint8_t v_v_64_; 
v_v_64_ = lean_ctor_get_uint8(v_val_63_, 0);
lean_dec_ref_known(v_val_63_, 0);
return v_v_64_;
}
else
{
uint8_t v___x_65_; 
lean_dec(v_val_63_);
v___x_65_ = lean_unbox(v_defValue_59_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_66_, lean_object* v_opt_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_66_, v_opt_67_);
lean_dec_ref(v_opt_67_);
lean_dec_ref(v_opts_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_74_ = l_Lean_MessageData_ofFormat(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_75_, lean_object* v_macroStack_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_options_79_; lean_object* v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; 
v_options_79_ = lean_ctor_get(v___y_77_, 2);
v___x_80_ = l_Lean_Elab_pp_macroStack;
v___x_81_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_79_, v___x_80_);
v___x_82_ = lean_bool_not(v___x_81_);
if (v___x_82_ == 0)
{
if (lean_obj_tag(v_macroStack_76_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_msgData_75_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_after_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_100_; 
v_head_84_ = lean_ctor_get(v_macroStack_76_, 0);
lean_inc(v_head_84_);
v_after_85_ = lean_ctor_get(v_head_84_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_head_84_, 0);
lean_dec(v_unused_101_);
v___x_87_ = v_head_84_;
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_after_85_);
lean_dec(v_head_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_89_);
lean_ctor_set(v___x_87_, 0, v_msgData_75_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_msgData_75_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_99_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_msgData_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_MessageData_ofSyntax(v_after_85_);
v___x_95_ = l_Lean_indentD(v___x_94_);
v_msgData_96_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_96_, 0, v___x_93_);
lean_ctor_set(v_msgData_96_, 1, v___x_95_);
v___x_97_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_96_, v_macroStack_76_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
else
{
lean_object* v___x_102_; 
lean_dec(v_macroStack_76_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_msgData_75_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_103_, lean_object* v_macroStack_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_103_, v_macroStack_104_, v___y_105_);
lean_dec_ref(v___y_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v___x_117_; lean_object* v_a_118_; lean_object* v_macroStack_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 5);
v___x_117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref(v___x_117_);
v_macroStack_119_ = lean_ctor_get(v___y_109_, 1);
v___x_120_ = l_Lean_Elab_getBetterRef(v_ref_116_, v_macroStack_119_);
lean_inc(v_macroStack_119_);
v___x_121_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_118_, v_macroStack_119_, v___y_113_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_120_);
lean_ctor_set(v___x_126_, 1, v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_145_ = l_Lean_stringToMessageData(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_fileName_153_; lean_object* v___x_154_; 
v_fileName_153_ = lean_ctor_get(v_a_150_, 0);
lean_inc_ref(v_fileName_153_);
v___x_154_ = l_System_FilePath_parent(v_fileName_153_);
if (lean_obj_tag(v___x_154_) == 1)
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_val_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 0);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_val_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v___x_154_);
v___x_163_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_153_);
v___x_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_164_, 0, v_fileName_153_);
v___x_165_ = l_Lean_MessageData_ofFormat(v___x_164_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_163_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_168_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_188_, v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_198_, lean_object* v_macroStack_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_198_, v_macroStack_199_, v___y_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_208_, lean_object* v_macroStack_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_208_, v_macroStack_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_218_, lean_object* v_cfg_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_System_FilePath_join(v_a_228_, v_lratPath_218_);
v___x_230_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_229_, v_cfg_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
return v___x_230_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_cfg_219_);
lean_dec_ref(v_lratPath_218_);
v_a_231_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_227_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_227_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_239_, lean_object* v_cfg_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_239_, v_cfg_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_249_, lean_object* v_ctx_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 9, 1);
lean_closure_set(v___x_256_, 0, v_ctx_250_);
v___x_257_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_249_, v___x_256_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_257_, 0);
lean_dec(v_unused_266_);
v___x_259_ = v___x_257_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_dec(v___x_257_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_257_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_275_, lean_object* v_ctx_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_275_, v_ctx_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_282_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_box(0);
v___x_284_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(v_00_u03b1_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_321_, uint8_t v_suppressElabErrors_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 1)
{
lean_object* v_pre_324_; 
v_pre_324_ = lean_ctor_get(v_x_323_, 0);
switch(lean_obj_tag(v_pre_324_))
{
case 1:
{
lean_object* v_pre_325_; 
v_pre_325_ = lean_ctor_get(v_pre_324_, 0);
switch(lean_obj_tag(v_pre_325_))
{
case 0:
{
lean_object* v_str_326_; lean_object* v_str_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_str_326_ = lean_ctor_get(v_x_323_, 1);
v_str_327_ = lean_ctor_get(v_pre_324_, 1);
v___x_328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_329_ = lean_string_dec_eq(v_str_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_331_ = lean_string_dec_eq(v_str_327_, v___x_330_);
if (v___x_331_ == 0)
{
return v___y_321_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_333_ = lean_string_dec_eq(v_str_326_, v___x_332_);
if (v___x_333_ == 0)
{
return v___y_321_;
}
else
{
return v_suppressElabErrors_322_;
}
}
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_335_ = lean_string_dec_eq(v_str_326_, v___x_334_);
if (v___x_335_ == 0)
{
return v___y_321_;
}
else
{
return v_suppressElabErrors_322_;
}
}
}
case 1:
{
lean_object* v_pre_336_; 
v_pre_336_ = lean_ctor_get(v_pre_325_, 0);
if (lean_obj_tag(v_pre_336_) == 0)
{
lean_object* v_str_337_; lean_object* v_str_338_; lean_object* v_str_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_str_337_ = lean_ctor_get(v_x_323_, 1);
v_str_338_ = lean_ctor_get(v_pre_324_, 1);
v_str_339_ = lean_ctor_get(v_pre_325_, 1);
v___x_340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_341_ = lean_string_dec_eq(v_str_339_, v___x_340_);
if (v___x_341_ == 0)
{
return v___y_321_;
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_343_ = lean_string_dec_eq(v_str_338_, v___x_342_);
if (v___x_343_ == 0)
{
return v___y_321_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6));
v___x_345_ = lean_string_dec_eq(v_str_337_, v___x_344_);
if (v___x_345_ == 0)
{
return v___y_321_;
}
else
{
return v_suppressElabErrors_322_;
}
}
}
}
else
{
return v___y_321_;
}
}
default: 
{
return v___y_321_;
}
}
}
case 0:
{
lean_object* v_str_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_str_346_ = lean_ctor_get(v_x_323_, 1);
v___x_347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7));
v___x_348_ = lean_string_dec_eq(v_str_346_, v___x_347_);
if (v___x_348_ == 0)
{
return v___y_321_;
}
else
{
return v_suppressElabErrors_322_;
}
}
default: 
{
return v___y_321_;
}
}
}
else
{
return v___y_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_349_, lean_object* v_suppressElabErrors_350_, lean_object* v_x_351_){
_start:
{
uint8_t v___y_6540__boxed_352_; uint8_t v_suppressElabErrors_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v___y_6540__boxed_352_ = lean_unbox(v___y_349_);
v_suppressElabErrors_boxed_353_ = lean_unbox(v_suppressElabErrors_350_);
v_res_354_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6540__boxed_352_, v_suppressElabErrors_boxed_353_, v_x_351_);
lean_dec(v_x_351_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_357_, lean_object* v_msgData_358_, uint8_t v_severity_359_, uint8_t v_isSilent_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___y_367_; uint8_t v___y_368_; uint8_t v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_403_; uint8_t v___y_404_; lean_object* v___y_405_; uint8_t v___y_406_; uint8_t v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_428_; lean_object* v___y_429_; uint8_t v___y_430_; uint8_t v___y_431_; uint8_t v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_439_; uint8_t v___y_440_; lean_object* v___y_441_; uint8_t v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; uint8_t v___y_445_; uint8_t v___x_450_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; uint8_t v___y_457_; uint8_t v___y_458_; uint8_t v___y_460_; uint8_t v___x_475_; 
v___x_450_ = 2;
v___x_475_ = l_Lean_instBEqMessageSeverity_beq(v_severity_359_, v___x_450_);
if (v___x_475_ == 0)
{
v___y_460_ = v___x_475_;
goto v___jp_459_;
}
else
{
uint8_t v___x_476_; 
lean_inc_ref(v_msgData_358_);
v___x_476_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_358_);
v___y_460_ = v___x_476_;
goto v___jp_459_;
}
v___jp_366_:
{
lean_object* v___x_376_; lean_object* v_currNamespace_377_; lean_object* v_openDecls_378_; lean_object* v_env_379_; lean_object* v_nextMacroScope_380_; lean_object* v_ngen_381_; lean_object* v_auxDeclNGen_382_; lean_object* v_traceState_383_; lean_object* v_cache_384_; lean_object* v_messages_385_; lean_object* v_infoState_386_; lean_object* v_snapshotTasks_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_401_; 
v___x_376_ = lean_st_ref_take(v___y_375_);
v_currNamespace_377_ = lean_ctor_get(v___y_374_, 6);
v_openDecls_378_ = lean_ctor_get(v___y_374_, 7);
v_env_379_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_380_ = lean_ctor_get(v___x_376_, 1);
v_ngen_381_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_382_ = lean_ctor_get(v___x_376_, 3);
v_traceState_383_ = lean_ctor_get(v___x_376_, 4);
v_cache_384_ = lean_ctor_get(v___x_376_, 5);
v_messages_385_ = lean_ctor_get(v___x_376_, 6);
v_infoState_386_ = lean_ctor_get(v___x_376_, 7);
v_snapshotTasks_387_ = lean_ctor_get(v___x_376_, 8);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_401_ == 0)
{
v___x_389_ = v___x_376_;
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snapshotTasks_387_);
lean_inc(v_infoState_386_);
lean_inc(v_messages_385_);
lean_inc(v_cache_384_);
lean_inc(v_traceState_383_);
lean_inc(v_auxDeclNGen_382_);
lean_inc(v_ngen_381_);
lean_inc(v_nextMacroScope_380_);
lean_inc(v_env_379_);
lean_dec(v___x_376_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
lean_inc(v_openDecls_378_);
lean_inc(v_currNamespace_377_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_currNamespace_377_);
lean_ctor_set(v___x_391_, 1, v_openDecls_378_);
v___x_392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___y_367_);
lean_inc_ref(v___y_370_);
lean_inc_ref(v___y_373_);
v___x_393_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_393_, 0, v___y_373_);
lean_ctor_set(v___x_393_, 1, v___y_371_);
lean_ctor_set(v___x_393_, 2, v___y_372_);
lean_ctor_set(v___x_393_, 3, v___y_370_);
lean_ctor_set(v___x_393_, 4, v___x_392_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*5, v___y_368_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*5 + 1, v___y_369_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*5 + 2, v_isSilent_360_);
v___x_394_ = l_Lean_MessageLog_add(v___x_393_, v_messages_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 6, v___x_394_);
v___x_396_ = v___x_389_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_env_379_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_nextMacroScope_380_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_ngen_381_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_auxDeclNGen_382_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_traceState_383_);
lean_ctor_set(v_reuseFailAlloc_400_, 5, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_400_, 6, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_400_, 7, v_infoState_386_);
lean_ctor_set(v_reuseFailAlloc_400_, 8, v_snapshotTasks_387_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_set(v___y_375_, v___x_396_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
v___jp_402_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_426_; 
v___x_411_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_358_);
v___x_412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_411_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_426_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc_ref_n(v___y_405_, 2);
v___x_417_ = l_Lean_FileMap_toPosition(v___y_405_, v___y_408_);
lean_dec(v___y_408_);
v___x_418_ = l_Lean_FileMap_toPosition(v___y_405_, v___y_410_);
lean_dec(v___y_410_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
v___x_420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0));
if (v___y_406_ == 0)
{
lean_del_object(v___x_415_);
lean_dec_ref(v___y_403_);
v___y_367_ = v_a_413_;
v___y_368_ = v___y_404_;
v___y_369_ = v___y_407_;
v___y_370_ = v___x_420_;
v___y_371_ = v___x_417_;
v___y_372_ = v___x_419_;
v___y_373_ = v___y_409_;
v___y_374_ = v___y_363_;
v___y_375_ = v___y_364_;
goto v___jp_366_;
}
else
{
uint8_t v___x_421_; 
lean_inc(v_a_413_);
v___x_421_ = l_Lean_MessageData_hasTag(v___y_403_, v_a_413_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec_ref_known(v___x_419_, 1);
lean_dec_ref(v___x_417_);
lean_dec(v_a_413_);
v___x_422_ = lean_box(0);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_422_);
v___x_424_ = v___x_415_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_del_object(v___x_415_);
v___y_367_ = v_a_413_;
v___y_368_ = v___y_404_;
v___y_369_ = v___y_407_;
v___y_370_ = v___x_420_;
v___y_371_ = v___x_417_;
v___y_372_ = v___x_419_;
v___y_373_ = v___y_409_;
v___y_374_ = v___y_363_;
v___y_375_ = v___y_364_;
goto v___jp_366_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Syntax_getTailPos_x3f(v___y_433_, v___y_430_);
lean_dec(v___y_433_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_inc(v___y_435_);
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_431_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_435_;
v___y_409_ = v___y_434_;
v___y_410_ = v___y_435_;
goto v___jp_402_;
}
else
{
lean_object* v_val_437_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_431_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_435_;
v___y_409_ = v___y_434_;
v___y_410_ = v_val_437_;
goto v___jp_402_;
}
}
v___jp_438_:
{
lean_object* v_ref_446_; lean_object* v___x_447_; 
v_ref_446_ = l_Lean_replaceRef(v_ref_357_, v___y_443_);
v___x_447_ = l_Lean_Syntax_getPos_x3f(v_ref_446_, v___y_440_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___y_428_ = v___y_439_;
v___y_429_ = v___y_441_;
v___y_430_ = v___y_440_;
v___y_431_ = v___y_442_;
v___y_432_ = v___y_445_;
v___y_433_ = v_ref_446_;
v___y_434_ = v___y_444_;
v___y_435_ = v___x_448_;
goto v___jp_427_;
}
else
{
lean_object* v_val_449_; 
v_val_449_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_447_, 1);
v___y_428_ = v___y_439_;
v___y_429_ = v___y_441_;
v___y_430_ = v___y_440_;
v___y_431_ = v___y_442_;
v___y_432_ = v___y_445_;
v___y_433_ = v_ref_446_;
v___y_434_ = v___y_444_;
v___y_435_ = v_val_449_;
goto v___jp_427_;
}
}
v___jp_451_:
{
if (v___y_458_ == 0)
{
v___y_439_ = v___y_454_;
v___y_440_ = v___y_457_;
v___y_441_ = v___y_452_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_455_;
v___y_444_ = v___y_456_;
v___y_445_ = v_severity_359_;
goto v___jp_438_;
}
else
{
v___y_439_ = v___y_454_;
v___y_440_ = v___y_457_;
v___y_441_ = v___y_452_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_455_;
v___y_444_ = v___y_456_;
v___y_445_ = v___x_450_;
goto v___jp_438_;
}
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_object* v_fileName_461_; lean_object* v_fileMap_462_; lean_object* v_options_463_; lean_object* v_ref_464_; uint8_t v_suppressElabErrors_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___f_468_; uint8_t v___x_469_; uint8_t v___x_470_; 
v_fileName_461_ = lean_ctor_get(v___y_363_, 0);
v_fileMap_462_ = lean_ctor_get(v___y_363_, 1);
v_options_463_ = lean_ctor_get(v___y_363_, 2);
v_ref_464_ = lean_ctor_get(v___y_363_, 5);
v_suppressElabErrors_465_ = lean_ctor_get_uint8(v___y_363_, sizeof(void*)*14 + 1);
v___x_466_ = lean_box(v___y_460_);
v___x_467_ = lean_box(v_suppressElabErrors_465_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_468_, 0, v___x_466_);
lean_closure_set(v___f_468_, 1, v___x_467_);
v___x_469_ = 1;
v___x_470_ = l_Lean_instBEqMessageSeverity_beq(v_severity_359_, v___x_469_);
if (v___x_470_ == 0)
{
v___y_452_ = v_fileMap_462_;
v___y_453_ = v_suppressElabErrors_465_;
v___y_454_ = v___f_468_;
v___y_455_ = v_ref_464_;
v___y_456_ = v_fileName_461_;
v___y_457_ = v___y_460_;
v___y_458_ = v___x_470_;
goto v___jp_451_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = l_Lean_warningAsError;
v___x_472_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_463_, v___x_471_);
v___y_452_ = v_fileMap_462_;
v___y_453_ = v_suppressElabErrors_465_;
v___y_454_ = v___f_468_;
v___y_455_ = v_ref_464_;
v___y_456_ = v_fileName_461_;
v___y_457_ = v___y_460_;
v___y_458_ = v___x_472_;
goto v___jp_451_;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref(v_msgData_358_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_477_, lean_object* v_msgData_478_, lean_object* v_severity_479_, lean_object* v_isSilent_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v_severity_boxed_486_; uint8_t v_isSilent_boxed_487_; lean_object* v_res_488_; 
v_severity_boxed_486_ = lean_unbox(v_severity_479_);
v_isSilent_boxed_487_ = lean_unbox(v_isSilent_480_);
v_res_488_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_477_, v_msgData_478_, v_severity_boxed_486_, v_isSilent_boxed_487_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v_ref_477_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_489_, uint8_t v_severity_490_, uint8_t v_isSilent_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; lean_object* v___x_498_; 
v_ref_497_ = lean_ctor_get(v___y_494_, 5);
v___x_498_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_497_, v_msgData_489_, v_severity_490_, v_isSilent_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_499_, lean_object* v_severity_500_, lean_object* v_isSilent_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v_severity_boxed_507_; uint8_t v_isSilent_boxed_508_; lean_object* v_res_509_; 
v_severity_boxed_507_ = lean_unbox(v_severity_500_);
v_isSilent_boxed_508_ = lean_unbox(v_isSilent_501_);
v_res_509_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_499_, v_severity_boxed_507_, v_isSilent_boxed_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; 
v___x_516_ = 1;
v___x_517_ = 0;
v___x_518_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_510_, v___x_516_, v___x_517_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(v_msgData_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(lean_object* v_a_535_, uint8_t v___x_536_, lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v_tk_541_, lean_object* v_a_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___y_553_; lean_object* v___x_565_; 
v___x_565_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_a_566_, v_a_535_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
if (lean_obj_tag(v_a_568_) == 0)
{
lean_object* v_ref_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_a_542_);
v_ref_569_ = lean_ctor_get(v___y_549_, 5);
v___x_570_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1);
v___x_571_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(v___x_570_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_592_; 
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_571_, 0);
lean_dec(v_unused_593_);
v___x_573_ = v___x_571_;
v_isShared_574_ = v_isSharedCheck_592_;
goto v_resetjp_572_;
}
else
{
lean_dec(v___x_571_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_592_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_575_ = l_Lean_SourceInfo_fromRef(v_ref_569_, v___x_536_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2));
lean_inc(v___x_575_);
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4));
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5));
v___x_580_ = l_Lean_Name_mkStr4(v___x_537_, v___x_538_, v___x_539_, v___x_579_);
v___x_581_ = l_Lean_Syntax_node2(v___x_575_, v___x_580_, v___x_577_, v___x_540_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_578_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
lean_ctor_set(v___x_584_, 4, v___x_583_);
lean_ctor_set(v___x_584_, 5, v___x_583_);
lean_inc(v_ref_569_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 1);
lean_ctor_set(v___x_573_, 0, v_ref_569_);
v___x_586_ = v___x_573_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_ref_569_);
v___x_586_ = v_reuseFailAlloc_591_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6));
v___x_588_ = 4;
v___x_589_ = l_Lean_MessageData_nil;
v___x_590_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_541_, v___x_584_, v___x_586_, v___x_587_, v___x_583_, v___x_588_, v___x_589_, v___y_549_, v___y_550_);
v___y_553_ = v___x_590_;
goto v___jp_552_;
}
}
}
else
{
lean_dec(v_tk_541_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_539_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___x_537_);
v___y_553_ = v___x_571_;
goto v___jp_552_;
}
}
else
{
lean_object* v_val_594_; lean_object* v___x_595_; 
lean_dec(v_tk_541_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_539_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___x_537_);
v_val_594_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v_a_568_, 1);
v___x_595_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_val_594_, v_a_542_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
v___y_553_ = v___x_595_;
goto v___jp_552_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_a_542_);
lean_dec(v_tk_541_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_539_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___x_537_);
v_a_596_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_567_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_567_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_a_542_);
lean_dec(v_tk_541_);
lean_dec(v___x_540_);
lean_dec_ref(v___x_539_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___x_537_);
v_a_604_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_565_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_565_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
v___jp_552_:
{
if (lean_obj_tag(v___y_553_) == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref_known(v___y_553_, 1);
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_554_, v___y_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_555_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v___x_555_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_dec(v___x_555_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
return v___x_555_;
}
}
else
{
return v___y_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed(lean_object** _args){
lean_object* v_a_612_ = _args[0];
lean_object* v___x_613_ = _args[1];
lean_object* v___x_614_ = _args[2];
lean_object* v___x_615_ = _args[3];
lean_object* v___x_616_ = _args[4];
lean_object* v___x_617_ = _args[5];
lean_object* v_tk_618_ = _args[6];
lean_object* v_a_619_ = _args[7];
lean_object* v___y_620_ = _args[8];
lean_object* v___y_621_ = _args[9];
lean_object* v___y_622_ = _args[10];
lean_object* v___y_623_ = _args[11];
lean_object* v___y_624_ = _args[12];
lean_object* v___y_625_ = _args[13];
lean_object* v___y_626_ = _args[14];
lean_object* v___y_627_ = _args[15];
lean_object* v___y_628_ = _args[16];
_start:
{
uint8_t v___x_6876__boxed_629_; lean_object* v_res_630_; 
v___x_6876__boxed_629_ = lean_unbox(v___x_613_);
v_res_630_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(v_a_612_, v___x_6876__boxed_629_, v___x_614_, v___x_615_, v___x_616_, v___x_617_, v_tk_618_, v_a_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_a_612_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_x_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0));
v___x_659_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1));
v___x_660_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_648_);
v___x_662_ = l_Lean_Syntax_isOfKind(v_x_648_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_x_648_);
v___x_663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = l_Lean_Syntax_getArg(v_x_648_, v___x_664_);
v___x_666_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_665_);
v___x_667_ = l_Lean_Syntax_isOfKind(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v___x_665_);
lean_dec(v_x_648_);
v___x_668_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v_path_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_669_ = lean_unsigned_to_nat(2u);
v_path_670_ = l_Lean_Syntax_getArg(v_x_648_, v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_670_);
v___x_672_ = l_Lean_Syntax_isOfKind(v_path_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v_path_670_);
lean_dec(v___x_665_);
lean_dec(v_x_648_);
v___x_673_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_673_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_674_ = lean_unsigned_to_nat(10u);
v___x_675_ = 0;
v___x_676_ = lean_unsigned_to_nat(100000u);
v___x_677_ = 0;
v___x_678_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_678_, 0, v___x_674_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 1, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 2, v___x_675_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 3, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 4, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 5, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 6, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 7, v___x_672_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 8, v___x_675_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 9, v___x_675_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*2 + 10, v___x_677_);
lean_inc(v___x_665_);
v___x_679_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_665_, v___x_678_, v___x_672_, v_a_649_, v_a_655_, v_a_656_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_n(v_a_680_, 2);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_TSyntax_getString(v_path_670_);
lean_dec(v_path_670_);
v___x_682_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_681_, v_a_680_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v_tk_685_; lean_object* v___x_686_; lean_object* v___f_687_; lean_object* v___x_688_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = lean_unsigned_to_nat(0u);
v_tk_685_ = l_Lean_Syntax_getArg(v_x_648_, v___x_684_);
lean_dec(v_x_648_);
v___x_686_ = lean_box(v___x_675_);
v___f_687_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed), 17, 8);
lean_closure_set(v___f_687_, 0, v_a_680_);
lean_closure_set(v___f_687_, 1, v___x_686_);
lean_closure_set(v___f_687_, 2, v___x_658_);
lean_closure_set(v___f_687_, 3, v___x_659_);
lean_closure_set(v___f_687_, 4, v___x_660_);
lean_closure_set(v___f_687_, 5, v___x_665_);
lean_closure_set(v___f_687_, 6, v_tk_685_);
lean_closure_set(v___f_687_, 7, v_a_683_);
v___x_688_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_687_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_688_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_a_680_);
lean_dec(v___x_665_);
lean_dec(v_x_648_);
v_a_689_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_682_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_682_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_path_670_);
lean_dec(v___x_665_);
lean_dec(v_x_648_);
v_a_697_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_679_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_679_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_x_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_727_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3));
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3));
v___x_730_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_731_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_727_, v___x_728_, v___x_729_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
return v_res_733_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_BVDecide(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
}
#ifdef __cplusplus
}
#endif

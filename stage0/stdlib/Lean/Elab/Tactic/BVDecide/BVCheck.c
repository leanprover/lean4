// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVCheck
// Imports: public import Lean.Elab.Tactic.BVDecide.BVDecide public import Lean.Meta.Tactic.TryThis import Lean.Meta.Tactic.BVDecide.TacticContext import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Sym.Util
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
lean_object* v_options_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_options_79_ = lean_ctor_get(v___y_77_, 2);
v___x_80_ = l_Lean_Elab_pp_macroStack;
v___x_81_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec(v_macroStack_76_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_msgData_75_);
return v___x_82_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_102_, lean_object* v_macroStack_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_102_, v_macroStack_103_, v___y_104_);
lean_dec_ref(v___y_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v_macroStack_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 5);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_107_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v_macroStack_118_ = lean_ctor_get(v___y_108_, 1);
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_115_, v_macroStack_118_);
lean_inc(v_macroStack_118_);
v___x_120_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_117_, v_macroStack_118_, v___y_112_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_fileName_152_; lean_object* v___x_153_; 
v_fileName_152_ = lean_ctor_get(v_a_149_, 0);
lean_inc_ref(v_fileName_152_);
v___x_153_ = l_System_FilePath_parent(v_fileName_152_);
if (lean_obj_tag(v___x_153_) == 1)
{
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_val_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_val_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v___x_153_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_152_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v_fileName_152_);
v___x_164_ = l_Lean_MessageData_ofFormat(v___x_163_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_167_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_177_, lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_187_, lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(v_00_u03b1_187_, v_msg_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_197_, lean_object* v_macroStack_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_197_, v_macroStack_198_, v___y_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_207_, lean_object* v_macroStack_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_207_, v_macroStack_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object* v_lratPath_217_, lean_object* v_cfg_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_System_FilePath_join(v_a_227_, v_lratPath_217_);
v___x_229_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v___x_228_, v_cfg_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v___x_229_;
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_cfg_218_);
lean_dec_ref(v_lratPath_217_);
v_a_230_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_226_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(lean_object* v_lratPath_238_, lean_object* v_cfg_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_lratPath_238_, v_cfg_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(lean_object* v_g_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_248_, v___x_249_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_268_);
v___x_262_ = v___x_260_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_dec(v___x_260_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_250_);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_250_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_260_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_260_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed(lean_object* v_g_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0(v_g_277_, v___x_278_, v___x_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(lean_object* v_g_290_, lean_object* v_hypotheses_291_, lean_object* v_ctx_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___f_302_; lean_object* v___x_303_; 
v___x_300_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed), 9, 1);
lean_closure_set(v___x_300_, 0, v_ctx_292_);
v___x_301_ = lean_box(0);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___lam__0___boxed), 12, 3);
lean_closure_set(v___f_302_, 0, v_g_290_);
lean_closure_set(v___f_302_, 1, v___x_300_);
lean_closure_set(v___f_302_, 2, v___x_301_);
v___x_303_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v___f_302_, v_hypotheses_291_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(lean_object* v_g_304_, lean_object* v_hypotheses_305_, lean_object* v_ctx_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_g_304_, v_hypotheses_305_, v_ctx_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(v_00_u03b1_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0(uint8_t v___y_353_, uint8_t v_suppressElabErrors_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 1)
{
lean_object* v_pre_356_; 
v_pre_356_ = lean_ctor_get(v_x_355_, 0);
switch(lean_obj_tag(v_pre_356_))
{
case 1:
{
lean_object* v_pre_357_; 
v_pre_357_ = lean_ctor_get(v_pre_356_, 0);
switch(lean_obj_tag(v_pre_357_))
{
case 0:
{
lean_object* v_str_358_; lean_object* v_str_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_str_358_ = lean_ctor_get(v_x_355_, 1);
v_str_359_ = lean_ctor_get(v_pre_356_, 1);
v___x_360_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__0));
v___x_361_ = lean_string_dec_eq(v_str_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1));
v___x_363_ = lean_string_dec_eq(v_str_359_, v___x_362_);
if (v___x_363_ == 0)
{
return v___y_353_;
}
else
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__2));
v___x_365_ = lean_string_dec_eq(v_str_358_, v___x_364_);
if (v___x_365_ == 0)
{
return v___y_353_;
}
else
{
return v_suppressElabErrors_354_;
}
}
}
else
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__3));
v___x_367_ = lean_string_dec_eq(v_str_358_, v___x_366_);
if (v___x_367_ == 0)
{
return v___y_353_;
}
else
{
return v_suppressElabErrors_354_;
}
}
}
case 1:
{
lean_object* v_pre_368_; 
v_pre_368_ = lean_ctor_get(v_pre_357_, 0);
if (lean_obj_tag(v_pre_368_) == 0)
{
lean_object* v_str_369_; lean_object* v_str_370_; lean_object* v_str_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_str_369_ = lean_ctor_get(v_x_355_, 1);
v_str_370_ = lean_ctor_get(v_pre_356_, 1);
v_str_371_ = lean_ctor_get(v_pre_357_, 1);
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__4));
v___x_373_ = lean_string_dec_eq(v_str_371_, v___x_372_);
if (v___x_373_ == 0)
{
return v___y_353_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__5));
v___x_375_ = lean_string_dec_eq(v_str_370_, v___x_374_);
if (v___x_375_ == 0)
{
return v___y_353_;
}
else
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__6));
v___x_377_ = lean_string_dec_eq(v_str_369_, v___x_376_);
if (v___x_377_ == 0)
{
return v___y_353_;
}
else
{
return v_suppressElabErrors_354_;
}
}
}
}
else
{
return v___y_353_;
}
}
default: 
{
return v___y_353_;
}
}
}
case 0:
{
lean_object* v_str_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_str_378_ = lean_ctor_get(v_x_355_, 1);
v___x_379_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__7));
v___x_380_ = lean_string_dec_eq(v_str_378_, v___x_379_);
if (v___x_380_ == 0)
{
return v___y_353_;
}
else
{
return v_suppressElabErrors_354_;
}
}
default: 
{
return v___y_353_;
}
}
}
else
{
return v___y_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v___y_381_, lean_object* v_suppressElabErrors_382_, lean_object* v_x_383_){
_start:
{
uint8_t v___y_22051__boxed_384_; uint8_t v_suppressElabErrors_boxed_385_; uint8_t v_res_386_; lean_object* v_r_387_; 
v___y_22051__boxed_384_ = lean_unbox(v___y_381_);
v_suppressElabErrors_boxed_385_ = lean_unbox(v_suppressElabErrors_382_);
v_res_386_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0(v___y_22051__boxed_384_, v_suppressElabErrors_boxed_385_, v_x_383_);
lean_dec(v_x_383_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_389_, lean_object* v_msgData_390_, uint8_t v_severity_391_, uint8_t v_isSilent_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; uint8_t v___y_404_; uint8_t v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; uint8_t v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; uint8_t v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; lean_object* v___y_471_; uint8_t v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; uint8_t v___y_477_; uint8_t v___x_482_; uint8_t v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; uint8_t v___y_490_; uint8_t v___y_492_; uint8_t v___x_507_; 
v___x_482_ = 2;
v___x_507_ = l_Lean_instBEqMessageSeverity_beq(v_severity_391_, v___x_482_);
if (v___x_507_ == 0)
{
v___y_492_ = v___x_507_;
goto v___jp_491_;
}
else
{
uint8_t v___x_508_; 
lean_inc_ref(v_msgData_390_);
v___x_508_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_390_);
v___y_492_ = v___x_508_;
goto v___jp_491_;
}
v___jp_398_:
{
lean_object* v___x_408_; lean_object* v_currNamespace_409_; lean_object* v_openDecls_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_traceState_415_; lean_object* v_cache_416_; lean_object* v_messages_417_; lean_object* v_infoState_418_; lean_object* v_snapshotTasks_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_433_; 
v___x_408_ = lean_st_ref_take(v___y_407_);
v_currNamespace_409_ = lean_ctor_get(v___y_406_, 6);
v_openDecls_410_ = lean_ctor_get(v___y_406_, 7);
v_env_411_ = lean_ctor_get(v___x_408_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_408_, 1);
v_ngen_413_ = lean_ctor_get(v___x_408_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_408_, 3);
v_traceState_415_ = lean_ctor_get(v___x_408_, 4);
v_cache_416_ = lean_ctor_get(v___x_408_, 5);
v_messages_417_ = lean_ctor_get(v___x_408_, 6);
v_infoState_418_ = lean_ctor_get(v___x_408_, 7);
v_snapshotTasks_419_ = lean_ctor_get(v___x_408_, 8);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_433_ == 0)
{
v___x_421_ = v___x_408_;
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snapshotTasks_419_);
lean_inc(v_infoState_418_);
lean_inc(v_messages_417_);
lean_inc(v_cache_416_);
lean_inc(v_traceState_415_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_408_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_openDecls_410_);
lean_inc(v_currNamespace_409_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_currNamespace_409_);
lean_ctor_set(v___x_423_, 1, v_openDecls_410_);
v___x_424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc_ref(v___y_400_);
v___x_425_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_425_, 0, v___y_400_);
lean_ctor_set(v___x_425_, 1, v___y_403_);
lean_ctor_set(v___x_425_, 2, v___y_399_);
lean_ctor_set(v___x_425_, 3, v___y_401_);
lean_ctor_set(v___x_425_, 4, v___x_424_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*5, v___y_404_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*5 + 1, v___y_405_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*5 + 2, v_isSilent_392_);
v___x_426_ = l_Lean_MessageLog_add(v___x_425_, v_messages_417_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 6, v___x_426_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_env_411_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_traceState_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_cache_416_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v_infoState_418_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_snapshotTasks_419_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_st_ref_set(v___y_407_, v___x_428_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
v___jp_434_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_458_; 
v___x_443_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_390_);
v___x_444_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_443_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_458_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_458_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref_n(v___y_439_, 2);
v___x_449_ = l_Lean_FileMap_toPosition(v___y_439_, v___y_438_);
lean_dec(v___y_438_);
v___x_450_ = l_Lean_FileMap_toPosition(v___y_439_, v___y_442_);
lean_dec(v___y_442_);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___closed__0));
if (v___y_436_ == 0)
{
lean_del_object(v___x_447_);
lean_dec_ref(v___y_435_);
v___y_399_ = v___x_451_;
v___y_400_ = v___y_437_;
v___y_401_ = v___x_452_;
v___y_402_ = v_a_445_;
v___y_403_ = v___x_449_;
v___y_404_ = v___y_440_;
v___y_405_ = v___y_441_;
v___y_406_ = v___y_395_;
v___y_407_ = v___y_396_;
goto v___jp_398_;
}
else
{
uint8_t v___x_453_; 
lean_inc(v_a_445_);
v___x_453_ = l_Lean_MessageData_hasTag(v___y_435_, v_a_445_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec_ref_known(v___x_451_, 1);
lean_dec_ref(v___x_449_);
lean_dec(v_a_445_);
v___x_454_ = lean_box(0);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_454_);
v___x_456_ = v___x_447_;
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
else
{
lean_del_object(v___x_447_);
v___y_399_ = v___x_451_;
v___y_400_ = v___y_437_;
v___y_401_ = v___x_452_;
v___y_402_ = v_a_445_;
v___y_403_ = v___x_449_;
v___y_404_ = v___y_440_;
v___y_405_ = v___y_441_;
v___y_406_ = v___y_395_;
v___y_407_ = v___y_396_;
goto v___jp_398_;
}
}
}
}
v___jp_459_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Syntax_getTailPos_x3f(v___y_461_, v___y_465_);
lean_dec(v___y_461_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_inc(v___y_467_);
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_464_;
v___y_440_ = v___y_465_;
v___y_441_ = v___y_466_;
v___y_442_ = v___y_467_;
goto v___jp_434_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v___y_435_ = v___y_460_;
v___y_436_ = v___y_462_;
v___y_437_ = v___y_463_;
v___y_438_ = v___y_467_;
v___y_439_ = v___y_464_;
v___y_440_ = v___y_465_;
v___y_441_ = v___y_466_;
v___y_442_ = v_val_469_;
goto v___jp_434_;
}
}
v___jp_470_:
{
lean_object* v_ref_478_; lean_object* v___x_479_; 
v_ref_478_ = l_Lean_replaceRef(v_ref_389_, v___y_475_);
v___x_479_ = l_Lean_Syntax_getPos_x3f(v_ref_478_, v___y_476_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___y_460_ = v___y_471_;
v___y_461_ = v_ref_478_;
v___y_462_ = v___y_472_;
v___y_463_ = v___y_473_;
v___y_464_ = v___y_474_;
v___y_465_ = v___y_476_;
v___y_466_ = v___y_477_;
v___y_467_ = v___x_480_;
goto v___jp_459_;
}
else
{
lean_object* v_val_481_; 
v_val_481_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_479_, 1);
v___y_460_ = v___y_471_;
v___y_461_ = v_ref_478_;
v___y_462_ = v___y_472_;
v___y_463_ = v___y_473_;
v___y_464_ = v___y_474_;
v___y_465_ = v___y_476_;
v___y_466_ = v___y_477_;
v___y_467_ = v_val_481_;
goto v___jp_459_;
}
}
v___jp_483_:
{
if (v___y_490_ == 0)
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_484_;
v___y_473_ = v___y_485_;
v___y_474_ = v___y_487_;
v___y_475_ = v___y_488_;
v___y_476_ = v___y_489_;
v___y_477_ = v_severity_391_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___y_486_;
v___y_472_ = v___y_484_;
v___y_473_ = v___y_485_;
v___y_474_ = v___y_487_;
v___y_475_ = v___y_488_;
v___y_476_ = v___y_489_;
v___y_477_ = v___x_482_;
goto v___jp_470_;
}
}
v___jp_491_:
{
if (v___y_492_ == 0)
{
lean_object* v_fileName_493_; lean_object* v_fileMap_494_; lean_object* v_options_495_; lean_object* v_ref_496_; uint8_t v_suppressElabErrors_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___f_500_; uint8_t v___x_501_; uint8_t v___x_502_; 
v_fileName_493_ = lean_ctor_get(v___y_395_, 0);
v_fileMap_494_ = lean_ctor_get(v___y_395_, 1);
v_options_495_ = lean_ctor_get(v___y_395_, 2);
v_ref_496_ = lean_ctor_get(v___y_395_, 5);
v_suppressElabErrors_497_ = lean_ctor_get_uint8(v___y_395_, sizeof(void*)*14 + 1);
v___x_498_ = lean_box(v___y_492_);
v___x_499_ = lean_box(v_suppressElabErrors_497_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_500_, 0, v___x_498_);
lean_closure_set(v___f_500_, 1, v___x_499_);
v___x_501_ = 1;
v___x_502_ = l_Lean_instBEqMessageSeverity_beq(v_severity_391_, v___x_501_);
if (v___x_502_ == 0)
{
v___y_484_ = v_suppressElabErrors_497_;
v___y_485_ = v_fileName_493_;
v___y_486_ = v___f_500_;
v___y_487_ = v_fileMap_494_;
v___y_488_ = v_ref_496_;
v___y_489_ = v___y_492_;
v___y_490_ = v___x_502_;
goto v___jp_483_;
}
else
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = l_Lean_warningAsError;
v___x_504_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_495_, v___x_503_);
v___y_484_ = v_suppressElabErrors_497_;
v___y_485_ = v_fileName_493_;
v___y_486_ = v___f_500_;
v___y_487_ = v_fileMap_494_;
v___y_488_ = v_ref_496_;
v___y_489_ = v___y_492_;
v___y_490_ = v___x_504_;
goto v___jp_483_;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec_ref(v_msgData_390_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_509_, lean_object* v_msgData_510_, lean_object* v_severity_511_, lean_object* v_isSilent_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_severity_boxed_518_; uint8_t v_isSilent_boxed_519_; lean_object* v_res_520_; 
v_severity_boxed_518_ = lean_unbox(v_severity_511_);
v_isSilent_boxed_519_ = lean_unbox(v_isSilent_512_);
v_res_520_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg(v_ref_509_, v_msgData_510_, v_severity_boxed_518_, v_isSilent_boxed_519_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v_ref_509_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_521_, uint8_t v_severity_522_, uint8_t v_isSilent_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_ref_533_; lean_object* v___x_534_; 
v_ref_533_ = lean_ctor_get(v___y_530_, 5);
v___x_534_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg(v_ref_533_, v_msgData_521_, v_severity_522_, v_isSilent_523_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_535_, lean_object* v_severity_536_, lean_object* v_isSilent_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v_severity_boxed_547_; uint8_t v_isSilent_boxed_548_; lean_object* v_res_549_; 
v_severity_boxed_547_ = lean_unbox(v_severity_536_);
v_isSilent_boxed_548_ = lean_unbox(v_isSilent_537_);
v_res_549_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_535_, v_severity_boxed_547_, v_isSilent_boxed_548_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = 1;
v___x_561_ = 0;
v___x_562_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_550_, v___x_560_, v___x_561_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(v_msgData_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_unsigned_to_nat(16u);
v___x_579_ = lean_mk_array(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(lean_object* v___x_589_, lean_object* v_a_590_, uint8_t v___x_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_tk_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___y_614_; lean_object* v___x_624_; 
v___x_606_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1);
v___x_607_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2);
lean_inc(v___x_589_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_589_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_inc_ref_n(v___x_608_, 3);
v___x_609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_589_);
lean_dec(v___x_589_);
v___x_611_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_611_, 0, v___x_606_);
lean_ctor_set(v___x_611_, 1, v___x_606_);
lean_ctor_set(v___x_611_, 2, v___x_606_);
lean_ctor_set(v___x_611_, 3, v___x_609_);
lean_ctor_set(v___x_611_, 4, v_a_590_);
lean_ctor_set(v___x_611_, 5, v___x_610_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*6, v___x_591_);
v___x_612_ = lean_st_mk_ref(v___x_611_);
v___x_624_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_a_592_, v___x_612_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; uint8_t v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_goal_629_; lean_object* v_hypotheses_630_; lean_object* v___x_631_; 
lean_dec(v_tk_598_);
lean_dec(v___x_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
lean_dec_ref(v___x_594_);
v___x_627_ = lean_st_ref_get(v___x_612_);
v___x_628_ = lean_st_ref_get(v___x_612_);
v_goal_629_ = lean_ctor_get(v___x_627_, 4);
lean_inc(v_goal_629_);
lean_dec(v___x_627_);
v_hypotheses_630_ = lean_ctor_get(v___x_628_, 5);
lean_inc_ref(v_hypotheses_630_);
lean_dec(v___x_628_);
v___x_631_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(v_goal_629_, v_hypotheses_630_, v_a_593_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
v___y_614_ = v___x_631_;
goto v___jp_613_;
}
else
{
lean_object* v_ref_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_a_593_);
v_ref_632_ = lean_ctor_get(v___y_603_, 5);
v___x_633_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4);
v___x_634_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(v___x_633_, v_a_592_, v___x_612_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_655_; 
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_656_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_638_ = l_Lean_SourceInfo_fromRef(v_ref_632_, v___x_591_);
v___x_639_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5));
lean_inc(v___x_638_);
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__7));
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__8));
v___x_643_ = l_Lean_Name_mkStr4(v___x_594_, v___x_595_, v___x_596_, v___x_642_);
v___x_644_ = l_Lean_Syntax_node2(v___x_638_, v___x_643_, v___x_640_, v___x_597_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_641_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
lean_ctor_set(v___x_647_, 3, v___x_646_);
lean_ctor_set(v___x_647_, 4, v___x_646_);
lean_ctor_set(v___x_647_, 5, v___x_646_);
lean_inc(v_ref_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 1);
lean_ctor_set(v___x_636_, 0, v_ref_632_);
v___x_649_ = v___x_636_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_ref_632_);
v___x_649_ = v_reuseFailAlloc_654_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__9));
v___x_651_ = 4;
v___x_652_ = l_Lean_MessageData_nil;
v___x_653_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_598_, v___x_647_, v___x_649_, v___x_650_, v___x_646_, v___x_651_, v___x_652_, v___y_603_, v___y_604_);
v___y_614_ = v___x_653_;
goto v___jp_613_;
}
}
}
else
{
lean_dec(v_tk_598_);
lean_dec(v___x_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
lean_dec_ref(v___x_594_);
v___y_614_ = v___x_634_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v___x_612_);
lean_dec(v_tk_598_);
lean_dec(v___x_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
lean_dec_ref(v___x_594_);
lean_dec_ref(v_a_593_);
v_a_657_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_624_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_624_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_613_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
v_a_615_ = lean_ctor_get(v___y_614_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___y_614_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v___y_614_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___y_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_st_ref_get(v___x_612_);
lean_dec(v___x_612_);
lean_dec(v___x_619_);
if (v_isShared_618_ == 0)
{
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_615_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_dec(v___x_612_);
return v___y_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed(lean_object** _args){
lean_object* v___x_665_ = _args[0];
lean_object* v_a_666_ = _args[1];
lean_object* v___x_667_ = _args[2];
lean_object* v_a_668_ = _args[3];
lean_object* v_a_669_ = _args[4];
lean_object* v___x_670_ = _args[5];
lean_object* v___x_671_ = _args[6];
lean_object* v___x_672_ = _args[7];
lean_object* v___x_673_ = _args[8];
lean_object* v_tk_674_ = _args[9];
lean_object* v___y_675_ = _args[10];
lean_object* v___y_676_ = _args[11];
lean_object* v___y_677_ = _args[12];
lean_object* v___y_678_ = _args[13];
lean_object* v___y_679_ = _args[14];
lean_object* v___y_680_ = _args[15];
lean_object* v___y_681_ = _args[16];
_start:
{
uint8_t v___x_22424__boxed_682_; lean_object* v_res_683_; 
v___x_22424__boxed_682_ = lean_unbox(v___x_667_);
v_res_683_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(v___x_665_, v_a_666_, v___x_22424__boxed_682_, v_a_668_, v_a_669_, v___x_670_, v___x_671_, v___x_672_, v___x_673_, v_tk_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v_a_668_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1(lean_object* v___x_684_, uint8_t v___x_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_tk_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_694_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_box(v___x_685_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed), 17, 10);
lean_closure_set(v___f_705_, 0, v___x_684_);
lean_closure_set(v___f_705_, 1, v_a_703_);
lean_closure_set(v___f_705_, 2, v___x_704_);
lean_closure_set(v___f_705_, 3, v_a_686_);
lean_closure_set(v___f_705_, 4, v_a_687_);
lean_closure_set(v___f_705_, 5, v___x_688_);
lean_closure_set(v___f_705_, 6, v___x_689_);
lean_closure_set(v___f_705_, 7, v___x_690_);
lean_closure_set(v___f_705_, 8, v___x_691_);
lean_closure_set(v___f_705_, 9, v_tk_692_);
v___x_706_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_705_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref_known(v___x_706_, 1);
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_707_, v___y_694_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_708_, 0);
lean_dec(v_unused_717_);
v___x_710_ = v___x_708_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_708_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
return v___x_708_;
}
}
else
{
return v___x_706_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_tk_692_);
lean_dec(v___x_691_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v___x_684_);
v_a_718_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_702_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_702_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1___boxed(lean_object** _args){
lean_object* v___x_726_ = _args[0];
lean_object* v___x_727_ = _args[1];
lean_object* v_a_728_ = _args[2];
lean_object* v_a_729_ = _args[3];
lean_object* v___x_730_ = _args[4];
lean_object* v___x_731_ = _args[5];
lean_object* v___x_732_ = _args[6];
lean_object* v___x_733_ = _args[7];
lean_object* v_tk_734_ = _args[8];
lean_object* v___y_735_ = _args[9];
lean_object* v___y_736_ = _args[10];
lean_object* v___y_737_ = _args[11];
lean_object* v___y_738_ = _args[12];
lean_object* v___y_739_ = _args[13];
lean_object* v___y_740_ = _args[14];
lean_object* v___y_741_ = _args[15];
lean_object* v___y_742_ = _args[16];
lean_object* v___y_743_ = _args[17];
_start:
{
uint8_t v___x_22601__boxed_744_; lean_object* v_res_745_; 
v___x_22601__boxed_744_ = lean_unbox(v___x_727_);
v_res_745_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1(v___x_726_, v___x_22601__boxed_744_, v_a_728_, v_a_729_, v___x_730_, v___x_731_, v___x_732_, v___x_733_, v_tk_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(lean_object* v_x_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0));
v___x_774_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1));
v___x_775_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg___lam__0___closed__1));
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_763_);
v___x_777_ = l_Lean_Syntax_isOfKind(v_x_763_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v_x_763_);
v___x_778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = l_Lean_Syntax_getArg(v_x_763_, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_780_);
v___x_782_ = l_Lean_Syntax_isOfKind(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec(v___x_780_);
lean_dec(v_x_763_);
v___x_783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v_path_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(2u);
v_path_785_ = l_Lean_Syntax_getArg(v_x_763_, v___x_784_);
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_785_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_path_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_path_785_);
lean_dec(v___x_780_);
lean_dec(v_x_763_);
v___x_788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_788_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_789_ = lean_unsigned_to_nat(10u);
v___x_790_ = 0;
v___x_791_ = lean_unsigned_to_nat(100000u);
v___x_792_ = 0;
v___x_793_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_793_, 0, v___x_789_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 1, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 2, v___x_790_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 3, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 4, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 5, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 6, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 7, v___x_787_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 8, v___x_790_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 9, v___x_790_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*2 + 10, v___x_792_);
lean_inc(v___x_780_);
v___x_794_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_780_, v___x_793_, v___x_787_, v_a_764_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_n(v_a_795_, 2);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = l_Lean_TSyntax_getString(v_path_785_);
lean_dec(v_path_785_);
v___x_797_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_796_, v_a_795_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v_tk_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_unsigned_to_nat(0u);
v_tk_800_ = l_Lean_Syntax_getArg(v_x_763_, v___x_799_);
lean_dec(v_x_763_);
v___x_801_ = lean_box(v___x_790_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__1___boxed), 18, 9);
lean_closure_set(v___f_802_, 0, v___x_799_);
lean_closure_set(v___f_802_, 1, v___x_801_);
lean_closure_set(v___f_802_, 2, v_a_795_);
lean_closure_set(v___f_802_, 3, v_a_798_);
lean_closure_set(v___f_802_, 4, v___x_773_);
lean_closure_set(v___f_802_, 5, v___x_774_);
lean_closure_set(v___f_802_, 6, v___x_775_);
lean_closure_set(v___f_802_, 7, v___x_780_);
lean_closure_set(v___f_802_, 8, v_tk_800_);
v___x_803_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_802_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_803_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_795_);
lean_dec(v___x_780_);
lean_dec(v_x_763_);
v_a_804_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_797_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_797_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_path_785_);
lean_dec(v___x_780_);
lean_dec(v_x_763_);
v_a_812_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_794_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_794_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object* v_x_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(v_x_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_831_, lean_object* v_msgData_832_, uint8_t v_severity_833_, uint8_t v_isSilent_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___redArg(v_ref_831_, v_msgData_832_, v_severity_833_, v_isSilent_834_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_845_, lean_object* v_msgData_846_, lean_object* v_severity_847_, lean_object* v_isSilent_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v_severity_boxed_858_; uint8_t v_isSilent_boxed_859_; lean_object* v_res_860_; 
v_severity_boxed_858_ = lean_unbox(v_severity_847_);
v_isSilent_boxed_859_ = lean_unbox(v_isSilent_848_);
v_res_860_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_845_, v_msgData_846_, v_severity_boxed_858_, v_isSilent_boxed_859_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v_ref_845_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_872_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_873_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3));
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3));
v___x_875_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_876_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_872_, v___x_873_, v___x_874_, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
return v_res_878_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Util(builtin);
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

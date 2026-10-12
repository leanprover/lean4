// Lean compiler output
// Module: Lean.Elab.CheckTactic
// Imports: public import Lean.Elab.Tactic.ElabTerm public import Lean.Elab.Command public import Lean.Elab.Tactic.Meta public import Lean.Meta.CheckTactic
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Term reduces to"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nbut is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3;
static const lean_array_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " closed goal, but is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " produced multiple goals, but is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkTactic"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(83, 196, 193, 73, 233, 22, 219, 16)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value;
static const lean_closure_object l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CheckTactic"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabCheckTactic"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 72, 15, 247, 239, 21, 78, 147)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(95) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(95) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " expected to fail on "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", but closed goal."};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ", but returned: "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ", but returned goals:"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "checkTacticFailure"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 178, 39, 246, 220, 9, 15, 154)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "elabCheckTacticFailure"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 111, 187, 142, 78, 109, 254, 147)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(73) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checkSimp"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 79, 163, 70, 127, 40, 174, 58)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "#check_tactic"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "~>"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandCheckSimp"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 31, 125, 199, 240, 147, 190, 74)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "checkSimpFailure"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 64, 91, 201, 12, 111, 199, 188)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value;
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "#check_tactic_failure"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expandCheckSimpFailure"};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 74, 202, 176, 97, 48, 121, 220)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(83) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_box(0), v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(v_00_u03b1_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_20_;
}
}
uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(lean_object* v_x_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_21_ = stack[0].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(v_x_21_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(v_x_24_);
lean_dec(v_x_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(lean_object* v_msgData_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_env_34_; uint8_t v___x_35_; lean_object* v_env_36_; lean_object* v___x_37_; lean_object* v_toCold_38_; lean_object* v_mctx_39_; lean_object* v_lctx_40_; lean_object* v_options_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_33_ = lean_st_ref_get(v___y_31_);
v_env_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc_ref(v_env_34_);
lean_dec(v___x_33_);
v___x_35_ = 0;
v_env_36_ = l_Lean_Environment_setRecordingDeps(v_env_34_, v___x_35_);
v___x_37_ = lean_st_ref_get(v___y_29_);
v_toCold_38_ = lean_ctor_get(v___y_30_, 0);
v_mctx_39_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_mctx_39_);
lean_dec(v___x_37_);
v_lctx_40_ = lean_ctor_get(v___y_28_, 2);
v_options_41_ = lean_ctor_get(v_toCold_38_, 2);
lean_inc_ref(v_options_41_);
lean_inc_ref(v_lctx_40_);
v___x_42_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_42_, 0, v_env_36_);
lean_ctor_set(v___x_42_, 1, v_mctx_39_);
lean_ctor_set(v___x_42_, 2, v_lctx_40_);
lean_ctor_set(v___x_42_, 3, v_options_41_);
v___x_43_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v_msgData_27_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msgData_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msgData_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_52_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_box(1);
v___x_54_ = l_Lean_MessageData_ofFormat(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2));
v___x_59_ = l_Lean_MessageData_ofFormat(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
return v_x_60_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_85_; 
v_head_62_ = lean_ctor_get(v_x_61_, 0);
v_tail_63_ = lean_ctor_get(v_x_61_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_61_);
if (v_isSharedCheck_85_ == 0)
{
v___x_65_ = v_x_61_;
v_isShared_66_ = v_isSharedCheck_85_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_tail_63_);
lean_inc(v_head_62_);
lean_dec(v_x_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_85_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_before_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_83_; 
v_before_67_ = lean_ctor_get(v_head_62_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_head_62_, 1);
lean_dec(v_unused_84_);
v___x_69_ = v_head_62_;
v_isShared_70_ = v_isSharedCheck_83_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_before_67_);
lean_dec(v_head_62_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_83_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 7);
lean_ctor_set(v___x_69_, 1, v___x_71_);
lean_ctor_set(v___x_69_, 0, v_x_60_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_x_60_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_82_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_74_);
lean_ctor_set(v___x_65_, 0, v___x_73_);
v___x_76_ = v___x_65_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_81_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = l_Lean_MessageData_ofSyntax(v_before_67_);
v___x_78_ = l_Lean_indentD(v___x_77_);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v_x_60_ = v___x_79_;
v_x_61_ = v_tail_63_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(lean_object* v_opts_86_, lean_object* v_opt_87_){
_start:
{
lean_object* v_name_88_; lean_object* v_defValue_89_; lean_object* v_map_90_; lean_object* v___x_91_; 
v_name_88_ = lean_ctor_get(v_opt_87_, 0);
v_defValue_89_ = lean_ctor_get(v_opt_87_, 1);
v_map_90_ = lean_ctor_get(v_opts_86_, 0);
v___x_91_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_90_, v_name_88_);
if (lean_obj_tag(v___x_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = lean_unbox(v_defValue_89_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; 
v_val_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v___x_91_, 1);
if (lean_obj_tag(v_val_93_) == 1)
{
uint8_t v_v_94_; 
v_v_94_ = lean_ctor_get_uint8(v_val_93_, 0);
lean_dec_ref_known(v_val_93_, 0);
return v_v_94_;
}
else
{
uint8_t v___x_95_; 
lean_dec(v_val_93_);
v___x_95_ = lean_unbox(v_defValue_89_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_86_ = stack[0].m_obj;
lean_object* v_opt_87_ = stack[1].m_obj;
uint8_t v_res_96_;
v_res_96_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_opts_86_, v_opt_87_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_opts_97_, lean_object* v_opt_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_opts_97_, v_opt_98_);
lean_dec_ref(v_opt_98_);
lean_dec_ref(v_opts_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_105_ = l_Lean_MessageData_ofFormat(v___x_104_);
return v___x_105_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_106_, lean_object* v_macroStack_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_108_);
v___x_111_ = l_Lean_Elab_pp_macroStack;
v___x_112_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v___x_110_, v___x_111_);
lean_dec_ref(v___x_110_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
lean_dec(v_macroStack_107_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_msgData_106_);
return v___x_113_;
}
else
{
if (lean_obj_tag(v_macroStack_107_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v_msgData_106_);
return v___x_114_;
}
else
{
lean_object* v_head_115_; lean_object* v_after_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_131_; 
v_head_115_ = lean_ctor_get(v_macroStack_107_, 0);
lean_inc(v_head_115_);
v_after_116_ = lean_ctor_get(v_head_115_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_head_115_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v_head_115_, 0);
lean_dec(v_unused_132_);
v___x_118_ = v_head_115_;
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_after_116_);
lean_dec(v_head_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 7);
lean_ctor_set(v___x_118_, 1, v___x_120_);
lean_ctor_set(v___x_118_, 0, v_msgData_106_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_msgData_106_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_130_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_msgData_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = l_Lean_MessageData_ofSyntax(v_after_116_);
v___x_126_ = l_Lean_indentD(v___x_125_);
v_msgData_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_127_, 0, v___x_124_);
lean_ctor_set(v_msgData_127_, 1, v___x_126_);
v___x_128_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(v_msgData_127_, v_macroStack_107_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_106_ = stack[0].m_obj;
lean_object* v_macroStack_107_ = stack[1].m_obj;
lean_object* v___y_108_ = stack[2].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_106_, v_macroStack_107_, v___y_108_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_134_, lean_object* v_macroStack_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_134_, v_macroStack_135_, v___y_136_);
lean_dec_ref(v___y_136_);
return v_res_138_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_ref_147_; lean_object* v_macroStack_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_ref_147_ = lean_ctor_get(v___y_144_, 2);
v_macroStack_148_ = lean_ctor_get(v___y_140_, 1);
v___x_149_ = l_Lean_Elab_getBetterRef(v_ref_147_, v_macroStack_148_);
v___x_150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msg_139_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v___x_150_);
lean_inc(v_macroStack_148_);
v___x_152_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_a_151_, v_macroStack_148_, v___y_144_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_149_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_139_ = stack[0].m_obj;
lean_object* v___y_140_ = stack[1].m_obj;
lean_object* v___y_141_ = stack[2].m_obj;
lean_object* v___y_142_ = stack[3].m_obj;
lean_object* v___y_143_ = stack[4].m_obj;
lean_object* v___y_144_ = stack[5].m_obj;
lean_object* v___y_145_ = stack[6].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_171_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object* v_ref_172_, lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_toCold_181_; lean_object* v_currRecDepth_182_; lean_object* v_ref_183_; uint16_t v_optionFlags_184_; uint8_t v_suppressElabErrors_185_; uint8_t v_isRecordingDeps_186_; lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_toCold_181_ = lean_ctor_get(v___y_178_, 0);
v_currRecDepth_182_ = lean_ctor_get(v___y_178_, 1);
v_ref_183_ = lean_ctor_get(v___y_178_, 2);
v_optionFlags_184_ = lean_ctor_get_uint16(v___y_178_, sizeof(void*)*3);
v_suppressElabErrors_185_ = lean_ctor_get_uint8(v___y_178_, sizeof(void*)*3 + 2);
v_isRecordingDeps_186_ = lean_ctor_get_uint8(v___y_178_, sizeof(void*)*3 + 3);
v_ref_187_ = l_Lean_replaceRef(v_ref_172_, v_ref_183_);
lean_inc(v_currRecDepth_182_);
lean_inc_ref(v_toCold_181_);
v___x_188_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_188_, 0, v_toCold_181_);
lean_ctor_set(v___x_188_, 1, v_currRecDepth_182_);
lean_ctor_set(v___x_188_, 2, v_ref_187_);
lean_ctor_set_uint16(v___x_188_, sizeof(void*)*3, v_optionFlags_184_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*3 + 2, v_suppressElabErrors_185_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*3 + 3, v_isRecordingDeps_186_);
v___x_189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___x_188_, v___y_179_);
lean_dec_ref_known(v___x_188_, 3);
return v___x_189_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_172_ = stack[0].m_obj;
lean_object* v_msg_173_ = stack[1].m_obj;
lean_object* v___y_174_ = stack[2].m_obj;
lean_object* v___y_175_ = stack[3].m_obj;
lean_object* v___y_176_ = stack[4].m_obj;
lean_object* v___y_177_ = stack[5].m_obj;
lean_object* v___y_178_ = stack[6].m_obj;
lean_object* v___y_179_ = stack[7].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_172_, v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object* v_ref_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_191_, v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v_ref_191_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* v_stx_218_, lean_object* v___x_219_, uint8_t v___x_220_, lean_object* v___x_221_, lean_object* v___f_222_, lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v___vars_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___y_234_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_box(v___x_220_);
v___x_265_ = lean_box(v___x_220_);
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_266_, 0, v___x_219_);
lean_closure_set(v___x_266_, 1, v___x_263_);
lean_closure_set(v___x_266_, 2, v___x_264_);
lean_closure_set(v___x_266_, 3, v___x_265_);
v___x_267_ = 1;
v___x_268_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_266_, v___x_267_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_n(v_a_269_, 2);
lean_dec_ref_known(v___x_268_, 1);
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
v___x_270_ = lean_infer_type(v_a_269_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_n(v_a_271_, 2);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_269_, v_a_271_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_a_273_);
v___x_275_ = 0;
v___x_276_ = lean_box(0);
v___x_277_ = l_Lean_Meta_mkFreshExprMVar(v___x_274_, v___x_275_, v___x_276_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_a_271_);
v___x_280_ = l_Lean_Elab_Term_elabTerm(v___x_221_, v___x_279_, v___x_220_, v___x_220_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_Expr_mvarId_x21(v_a_278_);
lean_dec(v_a_278_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_box(1);
v___x_285_ = 0;
v___x_286_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4));
v___x_287_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_287_, 0, v___x_263_);
lean_ctor_set(v___x_287_, 1, v___x_283_);
lean_ctor_set(v___x_287_, 2, v___x_263_);
lean_ctor_set(v___x_287_, 3, v___f_222_);
lean_ctor_set(v___x_287_, 4, v___x_284_);
lean_ctor_set(v___x_287_, 5, v___x_284_);
lean_ctor_set(v___x_287_, 6, v___x_263_);
lean_ctor_set(v___x_287_, 7, v___x_286_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8, v___x_220_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 1, v___x_220_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 2, v___x_220_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 3, v___x_220_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 4, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 5, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 6, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 7, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 8, v___x_220_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 9, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*8 + 10, v___x_220_);
v___x_288_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_288_, 0, v___x_223_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_283_);
lean_ctor_set(v___x_288_, 3, v___x_283_);
lean_ctor_set(v___x_288_, 4, v___x_283_);
lean_ctor_set(v___x_288_, 5, v___x_284_);
lean_ctor_set(v___x_288_, 6, v___x_283_);
lean_inc(v___x_224_);
v___x_289_ = l_Lean_Elab_runTactic(v___x_282_, v___x_224_, v___x_287_, v___x_288_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v_fst_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_396_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
v_fst_291_ = lean_ctor_get(v_a_290_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_a_290_, 1);
lean_dec(v_unused_397_);
v___x_293_ = v_a_290_;
v_isShared_294_ = v_isSharedCheck_396_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_fst_291_);
lean_dec(v_a_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_396_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
if (lean_obj_tag(v_fst_291_) == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = l_Lean_MessageData_ofSyntax(v___x_224_);
v___x_296_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 7);
lean_ctor_set(v___x_293_, 1, v___x_296_);
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_304_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_299_ = l_Lean_indentExpr(v_a_281_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_218_, v___x_302_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_303_;
}
}
else
{
lean_object* v_tail_305_; 
v_tail_305_ = lean_ctor_get(v_fst_291_, 1);
if (lean_obj_tag(v_tail_305_) == 0)
{
lean_object* v_head_306_; lean_object* v___x_307_; 
lean_del_object(v___x_293_);
lean_dec(v___x_224_);
v_head_306_ = lean_ctor_get(v_fst_291_, 0);
lean_inc(v_head_306_);
lean_dec_ref_known(v_fst_291_, 2);
v___x_307_ = l_Lean_MVarId_getType(v_head_306_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_218_, v_a_308_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_fst_311_; lean_object* v___y_313_; lean_object* v___x_343_; uint8_t v_transparency_344_; uint8_t v___x_345_; uint8_t v___x_346_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_fst_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_fst_311_);
lean_dec(v_a_310_);
v___x_343_ = l_Lean_Meta_Context_config(v___y_228_);
v_transparency_344_ = lean_ctor_get_uint8(v___x_343_, 9);
lean_dec_ref(v___x_343_);
v___x_345_ = 2;
v___x_346_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v_keyedConfig_347_; uint8_t v_trackZetaDelta_348_; lean_object* v_zetaDeltaSet_349_; lean_object* v_lctx_350_; lean_object* v_localInstances_351_; lean_object* v_defEqCtx_x3f_352_; lean_object* v_synthPendingDepth_353_; lean_object* v_customCanUnfoldPredicate_x3f_354_; uint8_t v_univApprox_355_; uint8_t v_inTypeClassResolution_356_; uint8_t v_cacheInferType_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_keyedConfig_347_ = lean_ctor_get(v___y_228_, 0);
v_trackZetaDelta_348_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7);
v_zetaDeltaSet_349_ = lean_ctor_get(v___y_228_, 1);
v_lctx_350_ = lean_ctor_get(v___y_228_, 2);
v_localInstances_351_ = lean_ctor_get(v___y_228_, 3);
v_defEqCtx_x3f_352_ = lean_ctor_get(v___y_228_, 4);
v_synthPendingDepth_353_ = lean_ctor_get(v___y_228_, 5);
v_customCanUnfoldPredicate_x3f_354_ = lean_ctor_get(v___y_228_, 6);
v_univApprox_355_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_356_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 2);
v_cacheInferType_357_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_347_);
v___x_358_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_345_, v_keyedConfig_347_);
lean_inc(v_customCanUnfoldPredicate_x3f_354_);
lean_inc(v_synthPendingDepth_353_);
lean_inc(v_defEqCtx_x3f_352_);
lean_inc_ref(v_localInstances_351_);
lean_inc_ref(v_lctx_350_);
lean_inc(v_zetaDeltaSet_349_);
v___x_359_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_zetaDeltaSet_349_);
lean_ctor_set(v___x_359_, 2, v_lctx_350_);
lean_ctor_set(v___x_359_, 3, v_localInstances_351_);
lean_ctor_set(v___x_359_, 4, v_defEqCtx_x3f_352_);
lean_ctor_set(v___x_359_, 5, v_synthPendingDepth_353_);
lean_ctor_set(v___x_359_, 6, v_customCanUnfoldPredicate_x3f_354_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7, v_trackZetaDelta_348_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 1, v_univApprox_355_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 2, v_inTypeClassResolution_356_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*7 + 3, v_cacheInferType_357_);
lean_inc(v_a_281_);
lean_inc(v_fst_311_);
v___x_360_ = l_Lean_Meta_isExprDefEq(v_fst_311_, v_a_281_, v___x_359_, v___y_229_, v___y_230_, v___y_231_);
lean_dec_ref_known(v___x_359_, 7);
v___y_313_ = v___x_360_;
goto v___jp_312_;
}
else
{
lean_object* v___x_361_; 
lean_inc(v_a_281_);
lean_inc(v_fst_311_);
v___x_361_ = l_Lean_Meta_isExprDefEq(v_fst_311_, v_a_281_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
v___y_313_ = v___x_361_;
goto v___jp_312_;
}
v___jp_312_:
{
if (lean_obj_tag(v___y_313_) == 0)
{
lean_object* v_a_314_; uint8_t v___x_315_; 
v_a_314_ = lean_ctor_get(v___y_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___y_313_, 1);
v___x_315_ = lean_unbox(v_a_314_);
lean_dec(v_a_314_);
if (v___x_315_ == 0)
{
if (v___x_220_ == 0)
{
lean_dec(v_fst_311_);
lean_dec(v_a_281_);
goto v___jp_260_;
}
else
{
lean_object* v___x_316_; uint8_t v_transparency_317_; uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_316_ = l_Lean_Meta_Context_config(v___y_228_);
v_transparency_317_ = lean_ctor_get_uint8(v___x_316_, 9);
lean_dec_ref(v___x_316_);
v___x_318_ = 2;
v___x_319_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v_keyedConfig_320_; uint8_t v_trackZetaDelta_321_; lean_object* v_zetaDeltaSet_322_; lean_object* v_lctx_323_; lean_object* v_localInstances_324_; lean_object* v_defEqCtx_x3f_325_; lean_object* v_synthPendingDepth_326_; lean_object* v_customCanUnfoldPredicate_x3f_327_; uint8_t v_univApprox_328_; uint8_t v_inTypeClassResolution_329_; uint8_t v_cacheInferType_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_keyedConfig_320_ = lean_ctor_get(v___y_228_, 0);
v_trackZetaDelta_321_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7);
v_zetaDeltaSet_322_ = lean_ctor_get(v___y_228_, 1);
v_lctx_323_ = lean_ctor_get(v___y_228_, 2);
v_localInstances_324_ = lean_ctor_get(v___y_228_, 3);
v_defEqCtx_x3f_325_ = lean_ctor_get(v___y_228_, 4);
v_synthPendingDepth_326_ = lean_ctor_get(v___y_228_, 5);
v_customCanUnfoldPredicate_x3f_327_ = lean_ctor_get(v___y_228_, 6);
v_univApprox_328_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_329_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 2);
v_cacheInferType_330_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_320_);
v___x_331_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_318_, v_keyedConfig_320_);
lean_inc(v_customCanUnfoldPredicate_x3f_327_);
lean_inc(v_synthPendingDepth_326_);
lean_inc(v_defEqCtx_x3f_325_);
lean_inc_ref(v_localInstances_324_);
lean_inc_ref(v_lctx_323_);
lean_inc(v_zetaDeltaSet_322_);
v___x_332_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_zetaDeltaSet_322_);
lean_ctor_set(v___x_332_, 2, v_lctx_323_);
lean_ctor_set(v___x_332_, 3, v_localInstances_324_);
lean_ctor_set(v___x_332_, 4, v_defEqCtx_x3f_325_);
lean_ctor_set(v___x_332_, 5, v_synthPendingDepth_326_);
lean_ctor_set(v___x_332_, 6, v_customCanUnfoldPredicate_x3f_327_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7, v_trackZetaDelta_321_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 1, v_univApprox_328_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 2, v_inTypeClassResolution_329_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 3, v_cacheInferType_330_);
v___x_333_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_311_, v_a_281_, v___x_332_, v___y_229_, v___y_230_, v___y_231_);
lean_dec_ref_known(v___x_332_, 7);
v___y_234_ = v___x_333_;
goto v___jp_233_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_311_, v_a_281_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
v___y_234_ = v___x_334_;
goto v___jp_233_;
}
}
}
else
{
lean_dec(v_fst_311_);
lean_dec(v_a_281_);
goto v___jp_260_;
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_fst_311_);
lean_dec(v_a_281_);
v_a_335_ = lean_ctor_get(v___y_313_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___y_313_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___y_313_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___y_313_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_281_);
v_a_362_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_309_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_309_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_a_281_);
v_a_370_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_307_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_307_);
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
lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_393_; 
v_isSharedCheck_393_ = !lean_is_exclusive(v_fst_291_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; lean_object* v_unused_395_; 
v_unused_394_ = lean_ctor_get(v_fst_291_, 1);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_fst_291_, 0);
lean_dec(v_unused_395_);
v___x_379_ = v_fst_291_;
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
else
{
lean_dec(v_fst_291_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = l_Lean_MessageData_ofSyntax(v___x_224_);
v___x_382_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 7);
lean_ctor_set(v___x_379_, 1, v___x_382_);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_392_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_indentExpr(v_a_281_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 7);
lean_ctor_set(v___x_293_, 1, v___x_385_);
lean_ctor_set(v___x_293_, 0, v___x_384_);
v___x_387_ = v___x_293_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_218_, v___x_389_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_390_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_a_281_);
lean_dec(v___x_224_);
v_a_398_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_289_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_289_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_a_278_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v___f_222_);
v_a_406_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_280_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_280_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_271_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v___f_222_);
lean_dec(v___x_221_);
v_a_414_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_277_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_277_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_271_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v___f_222_);
lean_dec(v___x_221_);
v_a_422_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_272_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_272_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_a_269_);
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v___f_222_);
lean_dec(v___x_221_);
v_a_430_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_270_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_270_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v___x_224_);
lean_dec(v___x_223_);
lean_dec_ref(v___f_222_);
lean_dec(v___x_221_);
v_a_438_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_268_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_268_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
v___jp_233_:
{
if (lean_obj_tag(v___y_234_) == 0)
{
lean_object* v_a_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_251_; 
v_a_235_ = lean_ctor_get(v___y_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___y_234_, 1);
v_fst_236_ = lean_ctor_get(v_a_235_, 0);
v_snd_237_ = lean_ctor_get(v_a_235_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_251_ == 0)
{
v___x_239_ = v_a_235_;
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
lean_dec(v_a_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1);
v___x_242_ = l_Lean_indentExpr(v_fst_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 7);
lean_ctor_set(v___x_239_, 1, v___x_242_);
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_250_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_indentExpr(v_snd_237_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_218_, v___x_248_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___y_234_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___y_234_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___y_234_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___y_234_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
v___jp_260_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_218_ = stack[0].m_obj;
lean_object* v___x_219_ = stack[1].m_obj;
uint8_t v___x_220_ = stack[2].m_num;
lean_object* v___x_221_ = stack[3].m_obj;
lean_object* v___f_222_ = stack[4].m_obj;
lean_object* v___x_223_ = stack[5].m_obj;
lean_object* v___x_224_ = stack[6].m_obj;
lean_object* v___vars_225_ = stack[7].m_obj;
lean_object* v___y_226_ = stack[8].m_obj;
lean_object* v___y_227_ = stack[9].m_obj;
lean_object* v___y_228_ = stack[10].m_obj;
lean_object* v___y_229_ = stack[11].m_obj;
lean_object* v___y_230_ = stack[12].m_obj;
lean_object* v___y_231_ = stack[13].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(v_stx_218_, v___x_219_, v___x_220_, v___x_221_, v___f_222_, v___x_223_, v___x_224_, v___vars_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* v_stx_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v___f_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v___vars_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_11584__boxed_462_; lean_object* v_res_463_; 
v___x_11584__boxed_462_ = lean_unbox(v___x_449_);
v_res_463_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(v_stx_447_, v___x_448_, v___x_11584__boxed_462_, v___x_450_, v___f_451_, v___x_452_, v___x_453_, v___vars_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v___vars_454_);
lean_dec(v_stx_447_);
return v_res_463_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(lean_object* v_env_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_messages_468_; lean_object* v_scopes_469_; lean_object* v_usedQuotCtxts_470_; lean_object* v_nextMacroScope_471_; lean_object* v_maxRecDepth_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_infoState_475_; lean_object* v_traceState_476_; lean_object* v_snapshotTasks_477_; lean_object* v_prevLinterStates_478_; lean_object* v_codeQualityEntryTasks_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_489_; 
v___x_467_ = lean_st_ref_take(v___y_465_);
v_messages_468_ = lean_ctor_get(v___x_467_, 1);
v_scopes_469_ = lean_ctor_get(v___x_467_, 2);
v_usedQuotCtxts_470_ = lean_ctor_get(v___x_467_, 3);
v_nextMacroScope_471_ = lean_ctor_get(v___x_467_, 4);
v_maxRecDepth_472_ = lean_ctor_get(v___x_467_, 5);
v_ngen_473_ = lean_ctor_get(v___x_467_, 6);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_467_, 7);
v_infoState_475_ = lean_ctor_get(v___x_467_, 8);
v_traceState_476_ = lean_ctor_get(v___x_467_, 9);
v_snapshotTasks_477_ = lean_ctor_get(v___x_467_, 10);
v_prevLinterStates_478_ = lean_ctor_get(v___x_467_, 11);
v_codeQualityEntryTasks_479_ = lean_ctor_get(v___x_467_, 12);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___x_467_, 0);
lean_dec(v_unused_490_);
v___x_481_ = v___x_467_;
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_codeQualityEntryTasks_479_);
lean_inc(v_prevLinterStates_478_);
lean_inc(v_snapshotTasks_477_);
lean_inc(v_traceState_476_);
lean_inc(v_infoState_475_);
lean_inc(v_auxDeclNGen_474_);
lean_inc(v_ngen_473_);
lean_inc(v_maxRecDepth_472_);
lean_inc(v_nextMacroScope_471_);
lean_inc(v_usedQuotCtxts_470_);
lean_inc(v_scopes_469_);
lean_inc(v_messages_468_);
lean_dec(v___x_467_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_box(0);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v_env_464_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_env_464_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v_scopes_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 3, v_usedQuotCtxts_470_);
lean_ctor_set(v_reuseFailAlloc_488_, 4, v_nextMacroScope_471_);
lean_ctor_set(v_reuseFailAlloc_488_, 5, v_maxRecDepth_472_);
lean_ctor_set(v_reuseFailAlloc_488_, 6, v_ngen_473_);
lean_ctor_set(v_reuseFailAlloc_488_, 7, v_auxDeclNGen_474_);
lean_ctor_set(v_reuseFailAlloc_488_, 8, v_infoState_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 9, v_traceState_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 10, v_snapshotTasks_477_);
lean_ctor_set(v_reuseFailAlloc_488_, 11, v_prevLinterStates_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 12, v_codeQualityEntryTasks_479_);
v___x_485_ = v_reuseFailAlloc_488_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_st_ref_put(v___y_465_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_483_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_464_ = stack[0].m_obj;
lean_object* v___y_465_ = stack[1].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_464_, v___y_465_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(lean_object* v_env_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_492_, v___y_493_);
lean_dec(v___y_493_);
return v_res_495_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(lean_object* v_env_496_, lean_object* v_x_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v_env_502_; lean_object* v_a_504_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_501_ = lean_st_ref_get(v___y_499_);
v_env_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_ref(v_env_502_);
lean_dec(v___x_501_);
v___x_514_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_496_, v___y_499_);
lean_dec_ref(v___x_514_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_515_ = lean_apply_3(v_x_497_, v___y_498_, v___y_499_, lean_box(0));
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_502_, v___y_499_);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_517_, 0);
lean_dec(v_unused_525_);
v___x_519_ = v___x_517_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_dec(v___x_517_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_a_516_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_516_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_515_, 1);
v_a_504_ = v_a_526_;
goto v___jp_503_;
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v___x_505_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_502_, v___y_499_);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_505_, 0);
lean_dec(v_unused_513_);
v___x_507_ = v___x_505_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_dec(v___x_505_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 1);
lean_ctor_set(v___x_507_, 0, v_a_504_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_496_ = stack[0].m_obj;
lean_object* v_x_497_ = stack[1].m_obj;
lean_object* v___y_498_ = stack[2].m_obj;
lean_object* v___y_499_ = stack[3].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_496_, v_x_497_, v___y_498_, v___y_499_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(lean_object* v_env_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_528_, v_x_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_533_;
}
}
lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* v_stx_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
lean_inc(v_stx_542_);
v___x_547_ = l_Lean_Syntax_isOfKind(v_stx_542_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_stx_542_);
v___x_548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_548_;
}
else
{
lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_env_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___f_549_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l_Lean_Syntax_getArg(v_stx_542_, v___x_550_);
v___x_552_ = lean_unsigned_to_nat(3u);
v___x_553_ = l_Lean_Syntax_getArg(v_stx_542_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(5u);
v___x_555_ = l_Lean_Syntax_getArg(v_stx_542_, v___x_554_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_box(v___x_547_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 15, 7);
lean_closure_set(v___f_558_, 0, v_stx_542_);
lean_closure_set(v___f_558_, 1, v___x_551_);
lean_closure_set(v___f_558_, 2, v___x_557_);
lean_closure_set(v___f_558_, 3, v___x_553_);
lean_closure_set(v___f_558_, 4, v___f_549_);
lean_closure_set(v___f_558_, 5, v___x_556_);
lean_closure_set(v___f_558_, 6, v___x_555_);
v___x_559_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_559_, 0, lean_box(0));
lean_closure_set(v___x_559_, 1, v___f_558_);
v___x_560_ = lean_st_ref_get(v_a_544_);
v_env_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_env_561_);
lean_dec(v___x_560_);
v___x_562_ = l_Lean_Environment_unlockAsync(v_env_561_);
v___x_563_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_562_, v___x_559_, v_a_543_, v_a_544_);
return v___x_563_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_542_ = stack[0].m_obj;
lean_object* v_a_543_ = stack[1].m_obj;
lean_object* v_a_544_ = stack[2].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_542_, v_a_543_, v_a_544_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(lean_object* v_stx_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_569_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object* v_00_u03b1_570_, lean_object* v_ref_571_, lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_571_, v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_571_ = stack[1].m_obj;
lean_object* v_msg_572_ = stack[2].m_obj;
lean_object* v___y_573_ = stack[3].m_obj;
lean_object* v___y_574_ = stack[4].m_obj;
lean_object* v___y_575_ = stack[5].m_obj;
lean_object* v___y_576_ = stack[6].m_obj;
lean_object* v___y_577_ = stack[7].m_obj;
lean_object* v___y_578_ = stack[8].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_box(0), v_ref_571_, v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object* v_00_u03b1_582_, lean_object* v_ref_583_, lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(v_00_u03b1_582_, v_ref_583_, v_msg_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v_ref_583_);
return v_res_592_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(lean_object* v_env_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_593_, v___y_595_);
return v___x_597_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_593_ = stack[0].m_obj;
lean_object* v___y_594_ = stack[1].m_obj;
lean_object* v___y_595_ = stack[2].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_593_, v___y_594_, v___y_595_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(lean_object* v_env_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_603_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_object* v_00_u03b1_604_, lean_object* v_env_605_, lean_object* v_x_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_605_, v_x_606_, v___y_607_, v___y_608_);
return v___x_610_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_605_ = stack[1].m_obj;
lean_object* v_x_606_ = stack[2].m_obj;
lean_object* v___y_607_ = stack[3].m_obj;
lean_object* v___y_608_ = stack[4].m_obj;
lean_object* v_res_611_;
v_res_611_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_box(0), v_env_605_, v_x_606_, v___y_607_, v___y_608_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(lean_object* v_00_u03b1_612_, lean_object* v_env_613_, lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(v_00_u03b1_612_, v_env_613_, v_x_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object* v_00_u03b1_619_, lean_object* v_msg_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_620_ = stack[1].m_obj;
lean_object* v___y_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v___y_624_ = stack[5].m_obj;
lean_object* v___y_625_ = stack[6].m_obj;
lean_object* v___y_626_ = stack[7].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_box(0), v_msg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object* v_00_u03b1_630_, lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(v_00_u03b1_630_, v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_639_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(lean_object* v_msgData_640_, lean_object* v_macroStack_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_640_, v_macroStack_641_, v___y_646_);
return v___x_649_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_640_ = stack[0].m_obj;
lean_object* v_macroStack_641_ = stack[1].m_obj;
lean_object* v___y_642_ = stack[2].m_obj;
lean_object* v___y_643_ = stack[3].m_obj;
lean_object* v___y_644_ = stack[4].m_obj;
lean_object* v___y_645_ = stack[5].m_obj;
lean_object* v___y_646_ = stack[6].m_obj;
lean_object* v___y_647_ = stack[7].m_obj;
lean_object* v_res_650_;
v_res_650_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_640_, v_macroStack_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_651_, lean_object* v_macroStack_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_651_, v_macroStack_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_660_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_671_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_672_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_673_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___boxed), 4, 0);
v___x_674_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_670_, v___x_671_, v___x_672_, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_675_;
v_res_675_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
stack->m_obj
 = v_res_675_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
return v_res_677_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6));
v___x_706_ = l_Lean_addBuiltinDeclarationRanges(v___x_704_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_707_;
v_res_707_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
return v_res_709_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(lean_object* v_a_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_710_ = stack[0].m_obj;
lean_object* v___y_711_ = stack[1].m_obj;
lean_object* v___y_712_ = stack[2].m_obj;
lean_object* v___y_713_ = stack[3].m_obj;
lean_object* v___y_714_ = stack[4].m_obj;
lean_object* v___y_715_ = stack[5].m_obj;
lean_object* v___y_716_ = stack[6].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(lean_object* v_a_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_728_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_object* v_00_u03b1_729_, lean_object* v_a_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_730_ = stack[1].m_obj;
lean_object* v___y_731_ = stack[2].m_obj;
lean_object* v___y_732_ = stack[3].m_obj;
lean_object* v___y_733_ = stack[4].m_obj;
lean_object* v___y_734_ = stack[5].m_obj;
lean_object* v___y_735_ = stack[6].m_obj;
lean_object* v___y_736_ = stack[7].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_box(0), v_a_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(lean_object* v_00_u03b1_740_, lean_object* v_a_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(v_00_u03b1_740_, v_a_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_749_;
}
}
lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Elab_runTactic(v___x_750_, v___x_751_, v___x_752_, v___x_753_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_761_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_761_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_750_ = stack[0].m_obj;
lean_object* v___x_751_ = stack[1].m_obj;
lean_object* v___x_752_ = stack[2].m_obj;
lean_object* v___x_753_ = stack[3].m_obj;
lean_object* v___y_754_ = stack[4].m_obj;
lean_object* v___y_755_ = stack[5].m_obj;
lean_object* v___y_756_ = stack[6].m_obj;
lean_object* v___y_757_ = stack[7].m_obj;
lean_object* v___y_758_ = stack[8].m_obj;
lean_object* v___y_759_ = stack[9].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(v___x_750_, v___x_751_, v___x_752_, v___x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v___x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(v___x_780_, v___x_781_, v___x_782_, v___x_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_791_;
}
}
lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* v_stx_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_x_793_);
return v___x_800_;
}
else
{
lean_object* v_head_801_; lean_object* v_tail_802_; lean_object* v___x_803_; 
v_head_801_ = lean_ctor_get(v_x_794_, 0);
lean_inc(v_head_801_);
v_tail_802_ = lean_ctor_get(v_x_794_, 1);
lean_inc(v_tail_802_);
lean_dec_ref_known(v_x_794_, 2);
v___x_803_ = l_Lean_MVarId_getType(v_head_801_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_792_, v_a_804_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v_fst_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_816_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v_fst_807_ = lean_ctor_get(v_a_806_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_a_806_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_a_806_, 1);
lean_dec(v_unused_817_);
v___x_809_ = v_a_806_;
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_fst_807_);
lean_dec(v_a_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_Lean_indentExpr(v_fst_807_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 7);
lean_ctor_set(v___x_809_, 1, v___x_811_);
lean_ctor_set(v___x_809_, 0, v_x_793_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_x_793_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v_x_793_ = v___x_813_;
v_x_794_ = v_tail_802_;
goto _start;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_tail_802_);
lean_dec_ref(v_x_793_);
v_a_818_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_805_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_805_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_tail_802_);
lean_dec_ref(v_x_793_);
v_a_826_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_803_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_803_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_792_ = stack[0].m_obj;
lean_object* v_x_793_ = stack[1].m_obj;
lean_object* v_x_794_ = stack[2].m_obj;
lean_object* v___y_795_ = stack[3].m_obj;
lean_object* v___y_796_ = stack[4].m_obj;
lean_object* v___y_797_ = stack[5].m_obj;
lean_object* v___y_798_ = stack[6].m_obj;
lean_object* v_res_834_;
v_res_834_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_792_, v_x_793_, v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
stack->m_obj
 = v_res_834_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* v_stx_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_835_, v_x_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_stx_835_);
return v_res_843_;
}
}
lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* v_stx_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_x_845_);
return v___x_854_;
}
else
{
lean_object* v_head_855_; lean_object* v_tail_856_; lean_object* v___x_857_; 
v_head_855_ = lean_ctor_get(v_x_846_, 0);
lean_inc(v_head_855_);
v_tail_856_ = lean_ctor_get(v_x_846_, 1);
lean_inc(v_tail_856_);
lean_dec_ref_known(v_x_846_, 2);
v___x_857_ = l_Lean_MVarId_getType(v_head_855_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_844_, v_a_858_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v_fst_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v_fst_861_ = lean_ctor_get(v_a_860_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_a_860_, 1);
lean_dec(v_unused_871_);
v___x_863_ = v_a_860_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_fst_861_);
lean_dec(v_a_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Lean_indentExpr(v_fst_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 7);
lean_ctor_set(v___x_863_, 1, v___x_865_);
lean_ctor_set(v___x_863_, 0, v_x_845_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_x_845_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_844_, v___x_867_, v_tail_856_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_868_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_tail_856_);
lean_dec_ref(v_x_845_);
v_a_872_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_859_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_859_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_tail_856_);
lean_dec_ref(v_x_845_);
v_a_880_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_857_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_857_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_844_ = stack[0].m_obj;
lean_object* v_x_845_ = stack[1].m_obj;
lean_object* v_x_846_ = stack[2].m_obj;
lean_object* v___y_847_ = stack[3].m_obj;
lean_object* v___y_848_ = stack[4].m_obj;
lean_object* v___y_849_ = stack[5].m_obj;
lean_object* v___y_850_ = stack[6].m_obj;
lean_object* v___y_851_ = stack[7].m_obj;
lean_object* v___y_852_ = stack[8].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_844_, v_x_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* v_stx_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_889_, v_x_890_, v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v_stx_889_);
return v_res_899_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_stx_914_, uint8_t v___x_915_, lean_object* v___f_916_, lean_object* v___x_917_, lean_object* v___vars_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___y_930_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(0);
lean_inc(v___x_913_);
v___x_1027_ = l_Lean_Elab_Term_elabTerm(v___x_913_, v___x_1026_, v___x_915_, v___x_915_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_n(v_a_1028_, 2);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
v___x_1029_ = lean_infer_type(v_a_1028_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_1028_, v_a_1030_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1032_);
v___x_1034_ = 0;
v___x_1035_ = lean_box(0);
v___x_1036_ = l_Lean_Meta_mkFreshExprMVar(v___x_1033_, v___x_1034_, v___x_1035_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_Lean_Expr_mvarId_x21(v_a_1037_);
lean_dec(v_a_1037_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_box(1);
v___x_1041_ = 0;
v___x_1042_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4));
v___x_1043_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1043_, 0, v___x_1026_);
lean_ctor_set(v___x_1043_, 1, v___x_1039_);
lean_ctor_set(v___x_1043_, 2, v___x_1026_);
lean_ctor_set(v___x_1043_, 3, v___f_916_);
lean_ctor_set(v___x_1043_, 4, v___x_1040_);
lean_ctor_set(v___x_1043_, 5, v___x_1040_);
lean_ctor_set(v___x_1043_, 6, v___x_1026_);
lean_ctor_set(v___x_1043_, 7, v___x_1042_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8, v___x_915_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 1, v___x_915_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 2, v___x_915_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 3, v___x_915_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 4, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 5, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 6, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 7, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 8, v___x_915_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 9, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*8 + 10, v___x_915_);
v___x_1044_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1044_, 0, v___x_917_);
lean_ctor_set(v___x_1044_, 1, v___x_1040_);
lean_ctor_set(v___x_1044_, 2, v___x_1039_);
lean_ctor_set(v___x_1044_, 3, v___x_1039_);
lean_ctor_set(v___x_1044_, 4, v___x_1039_);
lean_ctor_set(v___x_1044_, 5, v___x_1040_);
lean_ctor_set(v___x_1044_, 6, v___x_1039_);
lean_inc(v___x_912_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1045_, 0, v___x_1038_);
lean_closure_set(v___f_1045_, 1, v___x_912_);
lean_closure_set(v___f_1045_, 2, v___x_1043_);
lean_closure_set(v___f_1045_, 3, v___x_1044_);
v___x_1046_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_1045_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1046_) == 0)
{
v___y_930_ = v___x_1046_;
goto v___jp_929_;
}
else
{
lean_object* v_a_1047_; uint8_t v___y_1049_; uint8_t v___x_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v___x_1050_ = l_Lean_Exception_isInterrupt(v_a_1047_);
if (v___x_1050_ == 0)
{
uint8_t v___x_1051_; 
lean_inc(v_a_1047_);
v___x_1051_ = l_Lean_Exception_isRuntime(v_a_1047_);
v___y_1049_ = v___x_1051_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v___x_1050_;
goto v___jp_1048_;
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
lean_dec_ref_known(v___x_1046_, 1);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
goto v___jp_926_;
}
else
{
v___y_930_ = v___x_1046_;
goto v___jp_929_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v___x_917_);
lean_dec_ref(v___f_916_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_1052_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1036_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1036_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v___x_917_);
lean_dec_ref(v___f_916_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_1060_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1031_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1031_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1028_);
lean_dec(v___x_917_);
lean_dec_ref(v___f_916_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_1068_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1029_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1029_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v___x_917_);
lean_dec_ref(v___f_916_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_1076_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1027_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1027_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
v___jp_926_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
v___jp_929_:
{
if (lean_obj_tag(v___y_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___y_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___y_930_, 1);
if (lean_obj_tag(v_a_931_) == 0)
{
lean_dec(v___x_913_);
lean_dec(v___x_912_);
goto v___jp_926_;
}
else
{
lean_object* v_val_932_; lean_object* v_fst_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_1016_; 
v_val_932_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_a_931_, 1);
v_fst_933_ = lean_ctor_get(v_val_932_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_val_932_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v_val_932_, 1);
lean_dec(v_unused_1017_);
v___x_935_ = v_val_932_;
v_isShared_936_ = v_isSharedCheck_1016_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_fst_933_);
lean_dec(v_val_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_1016_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_fst_933_) == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = l_Lean_MessageData_ofSyntax(v___x_912_);
v___x_938_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 7);
lean_ctor_set(v___x_935_, 1, v___x_938_);
lean_ctor_set(v___x_935_, 0, v___x_937_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_946_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_941_ = l_Lean_MessageData_ofSyntax(v___x_913_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_914_, v___x_944_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_945_;
}
}
else
{
lean_object* v_tail_947_; 
v_tail_947_ = lean_ctor_get(v_fst_933_, 1);
if (lean_obj_tag(v_tail_947_) == 0)
{
lean_object* v_head_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_994_; 
v_head_948_ = lean_ctor_get(v_fst_933_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_fst_933_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v_fst_933_, 1);
lean_dec(v_unused_995_);
v___x_950_ = v_fst_933_;
v_isShared_951_ = v_isSharedCheck_994_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_head_948_);
lean_dec(v_fst_933_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_994_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_MVarId_getType(v_head_948_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_914_, v_a_953_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v_fst_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_976_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v_fst_956_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_a_955_, 1);
lean_dec(v_unused_977_);
v___x_958_ = v_a_955_;
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_fst_956_);
lean_dec(v_a_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_960_ = l_Lean_indentExpr(v_fst_956_);
v___x_961_ = l_Lean_MessageData_ofSyntax(v___x_912_);
v___x_962_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 7);
lean_ctor_set(v___x_958_, 1, v___x_962_);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_962_);
v___x_964_ = v_reuseFailAlloc_975_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_MessageData_ofSyntax(v___x_913_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 7);
lean_ctor_set(v___x_950_, 1, v___x_965_);
lean_ctor_set(v___x_950_, 0, v___x_964_);
v___x_967_ = v___x_950_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_974_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 7);
lean_ctor_set(v___x_935_, 1, v___x_968_);
lean_ctor_set(v___x_935_, 0, v___x_967_);
v___x_970_ = v___x_935_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_973_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_960_);
v___x_972_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_914_, v___x_971_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_del_object(v___x_950_);
lean_del_object(v___x_935_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_978_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_954_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_954_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_del_object(v___x_950_);
lean_del_object(v___x_935_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_986_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_952_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_952_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = l_Lean_MessageData_ofSyntax(v___x_912_);
v___x_997_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 7);
lean_ctor_set(v___x_935_, 1, v___x_997_);
lean_ctor_set(v___x_935_, 0, v___x_996_);
v___x_999_ = v___x_935_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1015_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1000_ = l_Lean_MessageData_ofSyntax(v___x_913_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_914_, v___x_1003_, v_fst_933_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_914_, v_a_1005_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1004_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v___x_913_);
lean_dec(v___x_912_);
v_a_1018_ = lean_ctor_get(v___y_930_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___y_930_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___y_930_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
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
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_912_ = stack[0].m_obj;
lean_object* v___x_913_ = stack[1].m_obj;
lean_object* v_stx_914_ = stack[2].m_obj;
uint8_t v___x_915_ = stack[3].m_num;
lean_object* v___f_916_ = stack[4].m_obj;
lean_object* v___x_917_ = stack[5].m_obj;
lean_object* v___vars_918_ = stack[6].m_obj;
lean_object* v___y_919_ = stack[7].m_obj;
lean_object* v___y_920_ = stack[8].m_obj;
lean_object* v___y_921_ = stack[9].m_obj;
lean_object* v___y_922_ = stack[10].m_obj;
lean_object* v___y_923_ = stack[11].m_obj;
lean_object* v___y_924_ = stack[12].m_obj;
lean_object* v_res_1084_;
v_res_1084_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(v___x_912_, v___x_913_, v_stx_914_, v___x_915_, v___f_916_, v___x_917_, v___vars_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
stack->m_obj
 = v_res_1084_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_stx_1087_, lean_object* v___x_1088_, lean_object* v___f_1089_, lean_object* v___x_1090_, lean_object* v___vars_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v___x_6698__boxed_1099_; lean_object* v_res_1100_; 
v___x_6698__boxed_1099_ = lean_unbox(v___x_1088_);
v_res_1100_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(v___x_1085_, v___x_1086_, v_stx_1087_, v___x_6698__boxed_1099_, v___f_1089_, v___x_1090_, v___vars_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___vars_1091_);
lean_dec(v_stx_1087_);
return v_res_1100_;
}
}
lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* v_stx_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
lean_inc(v_stx_1106_);
v___x_1111_ = l_Lean_Syntax_isOfKind(v_stx_1106_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_stx_1106_);
v___x_1112_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_1112_;
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_env_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___f_1113_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = l_Lean_Syntax_getArg(v_stx_1106_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(3u);
v___x_1117_ = l_Lean_Syntax_getArg(v_stx_1106_, v___x_1116_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_box(v___x_1111_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1120_, 0, v___x_1117_);
lean_closure_set(v___f_1120_, 1, v___x_1115_);
lean_closure_set(v___f_1120_, 2, v_stx_1106_);
lean_closure_set(v___f_1120_, 3, v___x_1119_);
lean_closure_set(v___f_1120_, 4, v___f_1113_);
lean_closure_set(v___f_1120_, 5, v___x_1118_);
v___x_1121_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_1121_, 0, lean_box(0));
lean_closure_set(v___x_1121_, 1, v___f_1120_);
v___x_1122_ = lean_st_ref_get(v_a_1108_);
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
v___x_1124_ = l_Lean_Environment_unlockAsync(v_env_1123_);
v___x_1125_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_1124_, v___x_1121_, v_a_1107_, v_a_1108_);
return v___x_1125_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_CheckTactic_elabCheckTacticFailure_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1106_ = stack[0].m_obj;
lean_object* v_a_1107_ = stack[1].m_obj;
lean_object* v_a_1108_ = stack[2].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_1106_, v_a_1107_, v_a_1108_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(lean_object* v_stx_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
return v_res_1131_;
}
}
lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* v_stx_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_1132_, v_x_1133_, v_x_1134_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1132_ = stack[0].m_obj;
lean_object* v_x_1133_ = stack[1].m_obj;
lean_object* v_x_1134_ = stack[2].m_obj;
lean_object* v___y_1135_ = stack[3].m_obj;
lean_object* v___y_1136_ = stack[4].m_obj;
lean_object* v___y_1137_ = stack[5].m_obj;
lean_object* v___y_1138_ = stack[6].m_obj;
lean_object* v___y_1139_ = stack[7].m_obj;
lean_object* v___y_1140_ = stack[8].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_1132_, v_x_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* v_stx_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_1144_, v_x_1145_, v_x_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v_stx_1144_);
return v_res_1154_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1163_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1164_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1165_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed), 4, 0);
v___x_1166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1167_;
v_res_1167_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
return v_res_1169_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6));
v___x_1198_ = l_Lean_addBuiltinDeclarationRanges(v___x_1196_, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1199_;
v_res_1199_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
return v_res_1201_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Array_mkArray0___redArg();
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* v_stx_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
lean_inc(v_stx_1227_);
v___x_1231_ = l_Lean_Syntax_isOfKind(v_stx_1227_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_stx_1227_);
v___x_1232_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1229_);
return v___x_1232_;
}
else
{
lean_object* v_ref_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_ref_1233_ = lean_ctor_get(v_a_1228_, 5);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = l_Lean_Syntax_getArg(v_stx_1227_, v___x_1234_);
v___x_1236_ = lean_unsigned_to_nat(3u);
v___x_1237_ = l_Lean_Syntax_getArg(v_stx_1227_, v___x_1236_);
lean_dec(v_stx_1227_);
v___x_1238_ = 0;
v___x_1239_ = l_Lean_SourceInfo_fromRef(v_ref_1233_, v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_1241_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2));
lean_inc_n(v___x_1239_, 7);
v___x_1242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1239_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3));
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1239_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1239_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1248_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1239_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
v___x_1250_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1251_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1252_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1239_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
lean_inc_ref_n(v___x_1253_, 4);
v___x_1254_ = l_Lean_Syntax_node1(v___x_1239_, v___x_1250_, v___x_1253_);
v___x_1255_ = l_Lean_Syntax_node6(v___x_1239_, v___x_1248_, v___x_1249_, v___x_1254_, v___x_1253_, v___x_1253_, v___x_1253_, v___x_1253_);
v___x_1256_ = l_Lean_Syntax_node6(v___x_1239_, v___x_1240_, v___x_1242_, v___x_1235_, v___x_1244_, v___x_1237_, v___x_1246_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_a_1229_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* v_stx_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_CheckTactic_expandCheckSimp(v_stx_1258_, v_a_1259_, v_a_1260_);
lean_dec_ref(v_a_1259_);
return v_res_1261_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1269_ = l_Lean_Elab_macroAttribute;
v___x_1270_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1272_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
v___x_1273_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1269_, v___x_1270_, v___x_1271_, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1274_;
v_res_1274_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
return v_res_1276_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6));
v___x_1305_ = l_Lean_addBuiltinDeclarationRanges(v___x_1303_, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1306_;
v_res_1306_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
stack->m_obj
 = v_res_1306_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* v_stx_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
lean_inc(v_stx_1315_);
v___x_1319_ = l_Lean_Syntax_isOfKind(v_stx_1315_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_stx_1315_);
v___x_1320_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1317_);
return v___x_1320_;
}
else
{
lean_object* v_ref_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_ref_1321_ = lean_ctor_get(v_a_1316_, 5);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = l_Lean_Syntax_getArg(v_stx_1315_, v___x_1322_);
lean_dec(v_stx_1315_);
v___x_1324_ = 0;
v___x_1325_ = l_Lean_SourceInfo_fromRef(v_ref_1321_, v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1327_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2));
lean_inc_n(v___x_1325_, 6);
v___x_1328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1325_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1325_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1332_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1325_);
lean_ctor_set(v___x_1333_, 1, v___x_1331_);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1335_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1336_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1325_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
lean_inc_ref_n(v___x_1337_, 4);
v___x_1338_ = l_Lean_Syntax_node1(v___x_1325_, v___x_1334_, v___x_1337_);
v___x_1339_ = l_Lean_Syntax_node6(v___x_1325_, v___x_1332_, v___x_1333_, v___x_1338_, v___x_1337_, v___x_1337_, v___x_1337_, v___x_1337_);
v___x_1340_ = l_Lean_Syntax_node4(v___x_1325_, v___x_1326_, v___x_1328_, v___x_1323_, v___x_1330_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_a_1317_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* v_stx_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(v_stx_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_a_1343_);
return v_res_1345_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1353_ = l_Lean_Elab_macroAttribute;
v___x_1354_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
v___x_1355_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1356_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
v___x_1357_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1353_, v___x_1354_, v___x_1355_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1358_;
v_res_1358_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
stack->m_obj
 = v_res_1358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
return v_res_1360_;
}
}
lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1388_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6));
v___x_1389_ = l_Lean_addBuiltinDeclarationRanges(v___x_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1390_;
v_res_1390_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
stack->m_obj
 = v_res_1390_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
return v_res_1392_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CheckTactic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_CheckTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_CheckTactic(builtin);
}
#ifdef __cplusplus
}
#endif

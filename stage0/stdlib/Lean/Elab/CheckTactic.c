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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
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
static const lean_array_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " closed goal, but is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Term reduces to"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nbut is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " produced multiple goals, but is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(v_x_21_);
lean_dec(v_x_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(lean_object* v_msgData_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; lean_object* v_env_31_; lean_object* v___x_32_; lean_object* v_mctx_33_; lean_object* v_lctx_34_; lean_object* v_options_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_30_ = lean_st_ref_get(v___y_28_);
v_env_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc_ref(v_env_31_);
lean_dec(v___x_30_);
v___x_32_ = lean_st_ref_get(v___y_26_);
v_mctx_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc_ref(v_mctx_33_);
lean_dec(v___x_32_);
v_lctx_34_ = lean_ctor_get(v___y_25_, 2);
v_options_35_ = lean_ctor_get(v___y_27_, 2);
lean_inc_ref(v_options_35_);
lean_inc_ref(v_lctx_34_);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v_env_31_);
lean_ctor_set(v___x_36_, 1, v_mctx_33_);
lean_ctor_set(v___x_36_, 2, v_lctx_34_);
lean_ctor_set(v___x_36_, 3, v_options_35_);
v___x_37_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v_msgData_24_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msgData_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_box(1);
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
return v_x_53_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_78_; 
v_head_55_ = lean_ctor_get(v_x_54_, 0);
v_tail_56_ = lean_ctor_get(v_x_54_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_78_ == 0)
{
v___x_58_ = v_x_54_;
v_isShared_59_ = v_isSharedCheck_78_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_head_55_);
lean_dec(v_x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_78_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_before_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_76_; 
v_before_60_ = lean_ctor_get(v_head_55_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_head_55_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v_head_55_, 1);
lean_dec(v_unused_77_);
v___x_62_ = v_head_55_;
v_isShared_63_ = v_isSharedCheck_76_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_before_60_);
lean_dec(v_head_55_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_76_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 7);
lean_ctor_set(v___x_62_, 1, v___x_64_);
lean_ctor_set(v___x_62_, 0, v_x_53_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_x_53_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_75_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 7);
lean_ctor_set(v___x_58_, 1, v___x_67_);
lean_ctor_set(v___x_58_, 0, v___x_66_);
v___x_69_ = v___x_58_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_74_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = l_Lean_MessageData_ofSyntax(v_before_60_);
v___x_71_ = l_Lean_indentD(v___x_70_);
v___x_72_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v_x_53_ = v___x_72_;
v_x_54_ = v_tail_56_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(lean_object* v_opts_79_, lean_object* v_opt_80_){
_start:
{
lean_object* v_name_81_; lean_object* v_defValue_82_; lean_object* v_map_83_; lean_object* v___x_84_; 
v_name_81_ = lean_ctor_get(v_opt_80_, 0);
v_defValue_82_ = lean_ctor_get(v_opt_80_, 1);
v_map_83_ = lean_ctor_get(v_opts_79_, 0);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_83_, v_name_81_);
if (lean_obj_tag(v___x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_unbox(v_defValue_82_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_84_, 1);
if (lean_obj_tag(v_val_86_) == 1)
{
uint8_t v_v_87_; 
v_v_87_ = lean_ctor_get_uint8(v_val_86_, 0);
lean_dec_ref_known(v_val_86_, 0);
return v_v_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec(v_val_86_);
v___x_88_ = lean_unbox(v_defValue_82_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_opts_89_, lean_object* v_opt_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_opts_89_, v_opt_90_);
lean_dec_ref(v_opt_90_);
lean_dec_ref(v_opts_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1));
v___x_97_ = l_Lean_MessageData_ofFormat(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_98_, lean_object* v_macroStack_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_options_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_options_102_ = lean_ctor_get(v___y_100_, 2);
v___x_103_ = l_Lean_Elab_pp_macroStack;
v___x_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_options_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
lean_dec(v_macroStack_99_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_msgData_98_);
return v___x_105_;
}
else
{
if (lean_obj_tag(v_macroStack_99_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v_msgData_98_);
return v___x_106_;
}
else
{
lean_object* v_head_107_; lean_object* v_after_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_123_; 
v_head_107_ = lean_ctor_get(v_macroStack_99_, 0);
lean_inc(v_head_107_);
v_after_108_ = lean_ctor_get(v_head_107_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_head_107_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v_head_107_, 0);
lean_dec(v_unused_124_);
v___x_110_ = v_head_107_;
v_isShared_111_ = v_isSharedCheck_123_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_after_108_);
lean_dec(v_head_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_123_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 7);
lean_ctor_set(v___x_110_, 1, v___x_112_);
lean_ctor_set(v___x_110_, 0, v_msgData_98_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_msgData_98_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_122_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_msgData_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_115_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_Lean_MessageData_ofSyntax(v_after_108_);
v___x_118_ = l_Lean_indentD(v___x_117_);
v_msgData_119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_119_, 0, v___x_116_);
lean_ctor_set(v_msgData_119_, 1, v___x_118_);
v___x_120_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(v_msgData_119_, v_macroStack_99_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_125_, lean_object* v_macroStack_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_125_, v_macroStack_126_, v___y_127_);
lean_dec_ref(v___y_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_ref_138_; lean_object* v___x_139_; lean_object* v_a_140_; lean_object* v_macroStack_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_152_; 
v_ref_138_ = lean_ctor_get(v___y_135_, 5);
v___x_139_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msg_130_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref(v___x_139_);
v_macroStack_141_ = lean_ctor_get(v___y_131_, 1);
v___x_142_ = l_Lean_Elab_getBetterRef(v_ref_138_, v_macroStack_141_);
lean_inc(v_macroStack_141_);
v___x_143_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_a_140_, v_macroStack_141_, v___y_135_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_152_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_142_);
lean_ctor_set(v___x_148_, 1, v_a_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 1);
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object* v_ref_162_, lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_fileName_171_; lean_object* v_fileMap_172_; lean_object* v_options_173_; lean_object* v_currRecDepth_174_; lean_object* v_maxRecDepth_175_; lean_object* v_ref_176_; lean_object* v_currNamespace_177_; lean_object* v_openDecls_178_; lean_object* v_initHeartbeats_179_; lean_object* v_maxHeartbeats_180_; lean_object* v_quotContext_181_; lean_object* v_currMacroScope_182_; uint8_t v_diag_183_; lean_object* v_cancelTk_x3f_184_; uint8_t v_suppressElabErrors_185_; lean_object* v_inheritedTraceOptions_186_; lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_fileName_171_ = lean_ctor_get(v___y_168_, 0);
v_fileMap_172_ = lean_ctor_get(v___y_168_, 1);
v_options_173_ = lean_ctor_get(v___y_168_, 2);
v_currRecDepth_174_ = lean_ctor_get(v___y_168_, 3);
v_maxRecDepth_175_ = lean_ctor_get(v___y_168_, 4);
v_ref_176_ = lean_ctor_get(v___y_168_, 5);
v_currNamespace_177_ = lean_ctor_get(v___y_168_, 6);
v_openDecls_178_ = lean_ctor_get(v___y_168_, 7);
v_initHeartbeats_179_ = lean_ctor_get(v___y_168_, 8);
v_maxHeartbeats_180_ = lean_ctor_get(v___y_168_, 9);
v_quotContext_181_ = lean_ctor_get(v___y_168_, 10);
v_currMacroScope_182_ = lean_ctor_get(v___y_168_, 11);
v_diag_183_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*14);
v_cancelTk_x3f_184_ = lean_ctor_get(v___y_168_, 12);
v_suppressElabErrors_185_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_186_ = lean_ctor_get(v___y_168_, 13);
v_ref_187_ = l_Lean_replaceRef(v_ref_162_, v_ref_176_);
lean_inc_ref(v_inheritedTraceOptions_186_);
lean_inc(v_cancelTk_x3f_184_);
lean_inc(v_currMacroScope_182_);
lean_inc(v_quotContext_181_);
lean_inc(v_maxHeartbeats_180_);
lean_inc(v_initHeartbeats_179_);
lean_inc(v_openDecls_178_);
lean_inc(v_currNamespace_177_);
lean_inc(v_maxRecDepth_175_);
lean_inc(v_currRecDepth_174_);
lean_inc_ref(v_options_173_);
lean_inc_ref(v_fileMap_172_);
lean_inc_ref(v_fileName_171_);
v___x_188_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_188_, 0, v_fileName_171_);
lean_ctor_set(v___x_188_, 1, v_fileMap_172_);
lean_ctor_set(v___x_188_, 2, v_options_173_);
lean_ctor_set(v___x_188_, 3, v_currRecDepth_174_);
lean_ctor_set(v___x_188_, 4, v_maxRecDepth_175_);
lean_ctor_set(v___x_188_, 5, v_ref_187_);
lean_ctor_set(v___x_188_, 6, v_currNamespace_177_);
lean_ctor_set(v___x_188_, 7, v_openDecls_178_);
lean_ctor_set(v___x_188_, 8, v_initHeartbeats_179_);
lean_ctor_set(v___x_188_, 9, v_maxHeartbeats_180_);
lean_ctor_set(v___x_188_, 10, v_quotContext_181_);
lean_ctor_set(v___x_188_, 11, v_currMacroScope_182_);
lean_ctor_set(v___x_188_, 12, v_cancelTk_x3f_184_);
lean_ctor_set(v___x_188_, 13, v_inheritedTraceOptions_186_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*14, v_diag_183_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*14 + 1, v_suppressElabErrors_185_);
v___x_189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___x_188_, v___y_169_);
lean_dec_ref_known(v___x_188_, 14);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object* v_ref_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_190_, v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v_ref_190_);
return v_res_199_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* v___x_217_, uint8_t v___x_218_, lean_object* v___x_219_, lean_object* v___f_220_, lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_stx_223_, lean_object* v___vars_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_box(v___x_218_);
v___x_237_ = lean_box(v___x_218_);
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_238_, 0, v___x_217_);
lean_closure_set(v___x_238_, 1, v___x_235_);
lean_closure_set(v___x_238_, 2, v___x_236_);
lean_closure_set(v___x_238_, 3, v___x_237_);
v___x_239_ = 1;
v___x_240_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_238_, v___x_239_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_n(v_a_241_, 2);
lean_dec_ref_known(v___x_240_, 1);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
v___x_242_ = lean_infer_type(v_a_241_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_n(v_a_243_, 2);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_241_, v_a_243_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_a_245_);
v___x_247_ = 0;
v___x_248_ = lean_box(0);
v___x_249_ = l_Lean_Meta_mkFreshExprMVar(v___x_246_, v___x_247_, v___x_248_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_a_243_);
v___x_252_ = l_Lean_Elab_Term_elabTerm(v___x_219_, v___x_251_, v___x_218_, v___x_218_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v___x_254_ = l_Lean_Expr_mvarId_x21(v_a_250_);
lean_dec(v_a_250_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_box(1);
v___x_257_ = 0;
v___x_258_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_259_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_259_, 0, v___x_235_);
lean_ctor_set(v___x_259_, 1, v___x_255_);
lean_ctor_set(v___x_259_, 2, v___x_235_);
lean_ctor_set(v___x_259_, 3, v___f_220_);
lean_ctor_set(v___x_259_, 4, v___x_256_);
lean_ctor_set(v___x_259_, 5, v___x_256_);
lean_ctor_set(v___x_259_, 6, v___x_235_);
lean_ctor_set(v___x_259_, 7, v___x_258_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8, v___x_218_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 1, v___x_218_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 2, v___x_218_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 3, v___x_218_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 4, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 5, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 6, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 7, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 8, v___x_218_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 9, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 10, v___x_218_);
v___x_260_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_260_, 0, v___x_221_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
lean_ctor_set(v___x_260_, 2, v___x_255_);
lean_ctor_set(v___x_260_, 3, v___x_255_);
lean_ctor_set(v___x_260_, 4, v___x_255_);
lean_ctor_set(v___x_260_, 5, v___x_256_);
lean_ctor_set(v___x_260_, 6, v___x_255_);
lean_inc(v___x_222_);
v___x_261_ = l_Lean_Elab_runTactic(v___x_254_, v___x_222_, v___x_259_, v___x_260_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_fst_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_387_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v_fst_263_ = lean_ctor_get(v_a_262_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_a_262_, 1);
lean_dec(v_unused_388_);
v___x_265_ = v_a_262_;
v_isShared_266_ = v_isSharedCheck_387_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_fst_263_);
lean_dec(v_a_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_387_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
if (lean_obj_tag(v_fst_263_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_267_ = l_Lean_MessageData_ofSyntax(v___x_222_);
v___x_268_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 7);
lean_ctor_set(v___x_265_, 1, v___x_268_);
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_276_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_271_ = l_Lean_indentExpr(v_a_253_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_223_, v___x_274_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_275_;
}
}
else
{
lean_object* v_tail_277_; 
v_tail_277_ = lean_ctor_get(v_fst_263_, 1);
if (lean_obj_tag(v_tail_277_) == 0)
{
lean_object* v_head_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_367_; 
lean_del_object(v___x_265_);
lean_dec(v___x_222_);
v_head_278_ = lean_ctor_get(v_fst_263_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_fst_263_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v_fst_263_, 1);
lean_dec(v_unused_368_);
v___x_280_ = v_fst_263_;
v_isShared_281_ = v_isSharedCheck_367_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_head_278_);
lean_dec(v_fst_263_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_367_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_MVarId_getType(v_head_278_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_223_, v_a_283_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_fst_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_349_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v_fst_286_ = lean_ctor_get(v_a_285_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_a_285_, 1);
lean_dec(v_unused_350_);
v___x_288_ = v_a_285_;
v_isShared_289_ = v_isSharedCheck_349_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_fst_286_);
lean_dec(v_a_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_349_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v_a_291_; lean_object* v_keyedConfig_322_; uint8_t v_trackZetaDelta_323_; lean_object* v_zetaDeltaSet_324_; lean_object* v_lctx_325_; lean_object* v_localInstances_326_; lean_object* v_defEqCtx_x3f_327_; lean_object* v_synthPendingDepth_328_; lean_object* v_customCanUnfoldPredicate_x3f_329_; uint8_t v_univApprox_330_; uint8_t v_inTypeClassResolution_331_; uint8_t v_cacheInferType_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_keyedConfig_322_ = lean_ctor_get(v___y_227_, 0);
v_trackZetaDelta_323_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*7);
v_zetaDeltaSet_324_ = lean_ctor_get(v___y_227_, 1);
v_lctx_325_ = lean_ctor_get(v___y_227_, 2);
v_localInstances_326_ = lean_ctor_get(v___y_227_, 3);
v_defEqCtx_x3f_327_ = lean_ctor_get(v___y_227_, 4);
v_synthPendingDepth_328_ = lean_ctor_get(v___y_227_, 5);
v_customCanUnfoldPredicate_x3f_329_ = lean_ctor_get(v___y_227_, 6);
v_univApprox_330_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_331_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*7 + 2);
v_cacheInferType_332_ = lean_ctor_get_uint8(v___y_227_, sizeof(void*)*7 + 3);
v___x_333_ = 2;
lean_inc_ref(v_keyedConfig_322_);
v___x_334_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_333_, v_keyedConfig_322_);
lean_inc(v_customCanUnfoldPredicate_x3f_329_);
lean_inc(v_synthPendingDepth_328_);
lean_inc(v_defEqCtx_x3f_327_);
lean_inc_ref(v_localInstances_326_);
lean_inc_ref(v_lctx_325_);
lean_inc(v_zetaDeltaSet_324_);
v___x_335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_zetaDeltaSet_324_);
lean_ctor_set(v___x_335_, 2, v_lctx_325_);
lean_ctor_set(v___x_335_, 3, v_localInstances_326_);
lean_ctor_set(v___x_335_, 4, v_defEqCtx_x3f_327_);
lean_ctor_set(v___x_335_, 5, v_synthPendingDepth_328_);
lean_ctor_set(v___x_335_, 6, v_customCanUnfoldPredicate_x3f_329_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*7, v_trackZetaDelta_323_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*7 + 1, v_univApprox_330_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*7 + 2, v_inTypeClassResolution_331_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*7 + 3, v_cacheInferType_332_);
lean_inc(v_a_253_);
lean_inc(v_fst_286_);
v___x_336_ = l_Lean_Meta_isExprDefEq(v_fst_286_, v_a_253_, v___x_335_, v___y_228_, v___y_229_, v___y_230_);
lean_dec_ref_known(v___x_335_, 7);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; uint8_t v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = lean_unbox(v_a_337_);
lean_dec(v_a_337_);
v_a_291_ = v___x_338_;
goto v___jp_290_;
}
else
{
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_339_; uint8_t v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_336_, 1);
v___x_340_ = lean_unbox(v_a_339_);
lean_dec(v_a_339_);
v_a_291_ = v___x_340_;
goto v___jp_290_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_del_object(v___x_288_);
lean_dec(v_fst_286_);
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v_a_341_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_336_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_336_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
v___jp_290_:
{
if (v_a_291_ == 0)
{
if (v___x_218_ == 0)
{
lean_del_object(v___x_288_);
lean_dec(v_fst_286_);
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
goto v___jp_232_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_286_, v_a_253_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_313_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v_fst_294_ = lean_ctor_get(v_a_293_, 0);
v_snd_295_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_313_ == 0)
{
v___x_297_ = v_a_293_;
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snd_295_);
lean_inc(v_fst_294_);
lean_dec(v_a_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_313_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6);
v___x_300_ = l_Lean_indentExpr(v_fst_294_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 7);
lean_ctor_set(v___x_297_, 1, v___x_300_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_302_ = v___x_297_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_312_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 7);
lean_ctor_set(v___x_288_, 1, v___x_303_);
lean_ctor_set(v___x_288_, 0, v___x_302_);
v___x_305_ = v___x_288_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_311_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = l_Lean_indentExpr(v_snd_295_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 7);
lean_ctor_set(v___x_280_, 1, v___x_306_);
lean_ctor_set(v___x_280_, 0, v___x_305_);
v___x_308_ = v___x_280_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_223_, v___x_308_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_del_object(v___x_288_);
lean_del_object(v___x_280_);
v_a_314_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_292_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_292_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_del_object(v___x_288_);
lean_dec(v_fst_286_);
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
goto v___jp_232_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v_a_351_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_284_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_284_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v_a_359_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_282_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_282_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
else
{
lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_384_; 
v_isSharedCheck_384_ = !lean_is_exclusive(v_fst_263_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; lean_object* v_unused_386_; 
v_unused_385_ = lean_ctor_get(v_fst_263_, 1);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_fst_263_, 0);
lean_dec(v_unused_386_);
v___x_370_ = v_fst_263_;
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
else
{
lean_dec(v_fst_263_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = l_Lean_MessageData_ofSyntax(v___x_222_);
v___x_373_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 7);
lean_ctor_set(v___x_370_, 1, v___x_373_);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = l_Lean_indentExpr(v_a_253_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 7);
lean_ctor_set(v___x_265_, 1, v___x_376_);
lean_ctor_set(v___x_265_, 0, v___x_375_);
v___x_378_ = v___x_265_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_223_, v___x_380_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_381_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_a_253_);
lean_dec(v___x_222_);
v_a_389_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_261_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_261_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_a_250_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___f_220_);
v_a_397_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_252_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_252_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_243_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___f_220_);
lean_dec(v___x_219_);
v_a_405_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_249_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_249_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
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
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_243_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___f_220_);
lean_dec(v___x_219_);
v_a_413_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_244_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_244_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_a_241_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___f_220_);
lean_dec(v___x_219_);
v_a_421_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_242_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_242_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___f_220_);
lean_dec(v___x_219_);
v_a_429_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_240_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_240_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___f_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_stx_443_, lean_object* v___vars_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_10902__boxed_452_; lean_object* v_res_453_; 
v___x_10902__boxed_452_ = lean_unbox(v___x_438_);
v_res_453_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(v___x_437_, v___x_10902__boxed_452_, v___x_439_, v___f_440_, v___x_441_, v___x_442_, v_stx_443_, v___vars_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___vars_444_);
lean_dec(v_stx_443_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(lean_object* v_env_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_messages_458_; lean_object* v_scopes_459_; lean_object* v_usedQuotCtxts_460_; lean_object* v_nextMacroScope_461_; lean_object* v_maxRecDepth_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_infoState_465_; lean_object* v_traceState_466_; lean_object* v_snapshotTasks_467_; lean_object* v_prevLinterStates_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v___x_457_ = lean_st_ref_take(v___y_455_);
v_messages_458_ = lean_ctor_get(v___x_457_, 1);
v_scopes_459_ = lean_ctor_get(v___x_457_, 2);
v_usedQuotCtxts_460_ = lean_ctor_get(v___x_457_, 3);
v_nextMacroScope_461_ = lean_ctor_get(v___x_457_, 4);
v_maxRecDepth_462_ = lean_ctor_get(v___x_457_, 5);
v_ngen_463_ = lean_ctor_get(v___x_457_, 6);
v_auxDeclNGen_464_ = lean_ctor_get(v___x_457_, 7);
v_infoState_465_ = lean_ctor_get(v___x_457_, 8);
v_traceState_466_ = lean_ctor_get(v___x_457_, 9);
v_snapshotTasks_467_ = lean_ctor_get(v___x_457_, 10);
v_prevLinterStates_468_ = lean_ctor_get(v___x_457_, 11);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_479_);
v___x_470_ = v___x_457_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_prevLinterStates_468_);
lean_inc(v_snapshotTasks_467_);
lean_inc(v_traceState_466_);
lean_inc(v_infoState_465_);
lean_inc(v_auxDeclNGen_464_);
lean_inc(v_ngen_463_);
lean_inc(v_maxRecDepth_462_);
lean_inc(v_nextMacroScope_461_);
lean_inc(v_usedQuotCtxts_460_);
lean_inc(v_scopes_459_);
lean_inc(v_messages_458_);
lean_dec(v___x_457_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_env_454_);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_env_454_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_messages_458_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_scopes_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_usedQuotCtxts_460_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_nextMacroScope_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_maxRecDepth_462_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v_ngen_463_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_auxDeclNGen_464_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v_infoState_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_traceState_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 10, v_snapshotTasks_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 11, v_prevLinterStates_468_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_st_ref_set(v___y_455_, v___x_473_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(lean_object* v_env_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_480_, v___y_481_);
lean_dec(v___y_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(lean_object* v_env_484_, lean_object* v_x_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v_env_490_; lean_object* v_a_492_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_489_ = lean_st_ref_get(v___y_487_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_env_490_);
lean_dec(v___x_489_);
v___x_502_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_484_, v___y_487_);
lean_dec_ref(v___x_502_);
lean_inc(v___y_487_);
lean_inc_ref(v___y_486_);
v___x_503_ = lean_apply_3(v_x_485_, v___y_486_, v___y_487_, lean_box(0));
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_490_, v___y_487_);
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
lean_ctor_set(v___x_507_, 0, v_a_504_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_503_, 1);
v_a_492_ = v_a_514_;
goto v___jp_491_;
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v___x_493_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_490_, v___y_487_);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_493_, 0);
lean_dec(v_unused_501_);
v___x_495_ = v___x_493_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_dec(v___x_493_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set_tag(v___x_495_, 1);
lean_ctor_set(v___x_495_, 0, v_a_492_);
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_492_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(lean_object* v_env_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_515_, v_x_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* v_stx_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
lean_inc(v_stx_529_);
v___x_534_ = l_Lean_Syntax_isOfKind(v_stx_529_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v_stx_529_);
v___x_535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v_env_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_536_ = lean_st_ref_get(v_a_531_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_env_537_);
lean_dec(v___x_536_);
v___f_538_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = l_Lean_Syntax_getArg(v_stx_529_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(3u);
v___x_542_ = l_Lean_Syntax_getArg(v_stx_529_, v___x_541_);
v___x_543_ = lean_unsigned_to_nat(5u);
v___x_544_ = l_Lean_Syntax_getArg(v_stx_529_, v___x_543_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_box(v___x_534_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 15, 7);
lean_closure_set(v___f_547_, 0, v___x_540_);
lean_closure_set(v___f_547_, 1, v___x_546_);
lean_closure_set(v___f_547_, 2, v___x_542_);
lean_closure_set(v___f_547_, 3, v___f_538_);
lean_closure_set(v___f_547_, 4, v___x_545_);
lean_closure_set(v___f_547_, 5, v___x_544_);
lean_closure_set(v___f_547_, 6, v_stx_529_);
v___x_548_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_548_, 0, lean_box(0));
lean_closure_set(v___x_548_, 1, v___f_547_);
v___x_549_ = l_Lean_Environment_unlockAsync(v_env_537_);
v___x_550_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_549_, v___x_548_, v_a_530_, v_a_531_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(lean_object* v_stx_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object* v_00_u03b1_556_, lean_object* v_ref_557_, lean_object* v_msg_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_557_, v_msg_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object* v_00_u03b1_567_, lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(v_00_u03b1_567_, v_ref_568_, v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v_ref_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(lean_object* v_env_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_578_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(lean_object* v_env_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_object* v_00_u03b1_588_, lean_object* v_env_589_, lean_object* v_x_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_589_, v_x_590_, v___y_591_, v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(lean_object* v_00_u03b1_595_, lean_object* v_env_596_, lean_object* v_x_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(v_00_u03b1_595_, v_env_596_, v_x_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object* v_00_u03b1_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object* v_00_u03b1_612_, lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(v_00_u03b1_612_, v_msg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(lean_object* v_msgData_622_, lean_object* v_macroStack_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_622_, v_macroStack_623_, v___y_628_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_632_, lean_object* v_macroStack_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_632_, v_macroStack_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_652_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_654_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___boxed), 4, 0);
v___x_655_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_651_, v___x_652_, v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6));
v___x_686_ = l_Lean_addBuiltinDeclarationRanges(v___x_684_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(lean_object* v_a_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(lean_object* v_a_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_object* v_00_u03b1_707_, lean_object* v_a_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(lean_object* v_00_u03b1_717_, lean_object* v_a_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(v_00_u03b1_717_, v_a_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Elab_runTactic(v___x_727_, v___x_728_, v___x_729_, v___x_730_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_a_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_738_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* v___x_756_, lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v___x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(v___x_756_, v___x_757_, v___x_758_, v___x_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* v_stx_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_x_769_);
return v___x_776_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; 
v_head_777_ = lean_ctor_get(v_x_770_, 0);
lean_inc(v_head_777_);
v_tail_778_ = lean_ctor_get(v_x_770_, 1);
lean_inc(v_tail_778_);
lean_dec_ref_known(v_x_770_, 2);
v___x_779_ = l_Lean_MVarId_getType(v_head_777_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_768_, v_a_780_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v_fst_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_792_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_fst_783_ = lean_ctor_get(v_a_782_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_a_782_, 1);
lean_dec(v_unused_793_);
v___x_785_ = v_a_782_;
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_fst_783_);
lean_dec(v_a_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = l_Lean_indentExpr(v_fst_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 7);
lean_ctor_set(v___x_785_, 1, v___x_787_);
lean_ctor_set(v___x_785_, 0, v_x_769_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_x_769_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_791_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v_x_769_ = v___x_789_;
v_x_770_ = v_tail_778_;
goto _start;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_tail_778_);
lean_dec_ref(v_x_769_);
v_a_794_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_781_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_781_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_tail_778_);
lean_dec_ref(v_x_769_);
v_a_802_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_779_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_779_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* v_stx_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_810_, v_x_811_, v_x_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v_stx_810_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* v_stx_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_x_820_);
return v___x_829_;
}
else
{
lean_object* v_head_830_; lean_object* v_tail_831_; lean_object* v___x_832_; 
v_head_830_ = lean_ctor_get(v_x_821_, 0);
lean_inc(v_head_830_);
v_tail_831_ = lean_ctor_get(v_x_821_, 1);
lean_inc(v_tail_831_);
lean_dec_ref_known(v_x_821_, 2);
v___x_832_ = l_Lean_MVarId_getType(v_head_830_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_819_, v_a_833_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_845_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v_fst_836_ = lean_ctor_get(v_a_835_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_835_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_a_835_, 1);
lean_dec(v_unused_846_);
v___x_838_ = v_a_835_;
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_fst_836_);
lean_dec(v_a_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_845_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_indentExpr(v_fst_836_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 7);
lean_ctor_set(v___x_838_, 1, v___x_840_);
lean_ctor_set(v___x_838_, 0, v_x_820_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_x_820_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_819_, v___x_842_, v_tail_831_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_843_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_tail_831_);
lean_dec_ref(v_x_820_);
v_a_847_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_834_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_834_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_tail_831_);
lean_dec_ref(v_x_820_);
v_a_855_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_832_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_832_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* v_stx_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_863_, v_x_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v_stx_863_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* v___x_886_, uint8_t v___x_887_, lean_object* v___x_888_, lean_object* v_stx_889_, lean_object* v___f_890_, lean_object* v___x_891_, lean_object* v___vars_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___y_904_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_box(0);
lean_inc(v___x_886_);
v___x_1001_ = l_Lean_Elab_Term_elabTerm(v___x_886_, v___x_1000_, v___x_887_, v___x_887_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_n(v_a_1002_, 2);
lean_dec_ref_known(v___x_1001_, 1);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
v___x_1003_ = lean_infer_type(v_a_1002_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_1002_, v_a_1004_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_a_1006_);
v___x_1008_ = 0;
v___x_1009_ = lean_box(0);
v___x_1010_ = l_Lean_Meta_mkFreshExprMVar(v___x_1007_, v___x_1008_, v___x_1009_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = l_Lean_Expr_mvarId_x21(v_a_1011_);
lean_dec(v_a_1011_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_box(1);
v___x_1015_ = 0;
v___x_1016_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_1017_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1017_, 0, v___x_1000_);
lean_ctor_set(v___x_1017_, 1, v___x_1013_);
lean_ctor_set(v___x_1017_, 2, v___x_1000_);
lean_ctor_set(v___x_1017_, 3, v___f_890_);
lean_ctor_set(v___x_1017_, 4, v___x_1014_);
lean_ctor_set(v___x_1017_, 5, v___x_1014_);
lean_ctor_set(v___x_1017_, 6, v___x_1000_);
lean_ctor_set(v___x_1017_, 7, v___x_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8, v___x_887_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 1, v___x_887_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 2, v___x_887_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 3, v___x_887_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 4, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 5, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 6, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 7, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 8, v___x_887_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 9, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*8 + 10, v___x_887_);
v___x_1018_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1018_, 0, v___x_891_);
lean_ctor_set(v___x_1018_, 1, v___x_1014_);
lean_ctor_set(v___x_1018_, 2, v___x_1013_);
lean_ctor_set(v___x_1018_, 3, v___x_1013_);
lean_ctor_set(v___x_1018_, 4, v___x_1013_);
lean_ctor_set(v___x_1018_, 5, v___x_1014_);
lean_ctor_set(v___x_1018_, 6, v___x_1013_);
lean_inc(v___x_888_);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1019_, 0, v___x_1012_);
lean_closure_set(v___f_1019_, 1, v___x_888_);
lean_closure_set(v___f_1019_, 2, v___x_1017_);
lean_closure_set(v___f_1019_, 3, v___x_1018_);
v___x_1020_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_1019_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_1020_) == 0)
{
v___y_904_ = v___x_1020_;
goto v___jp_903_;
}
else
{
lean_object* v_a_1021_; uint8_t v___y_1023_; uint8_t v___x_1024_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
v___x_1024_ = l_Lean_Exception_isInterrupt(v_a_1021_);
if (v___x_1024_ == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Lean_Exception_isRuntime(v_a_1021_);
v___y_1023_ = v___x_1025_;
goto v___jp_1022_;
}
else
{
lean_dec(v_a_1021_);
v___y_1023_ = v___x_1024_;
goto v___jp_1022_;
}
v___jp_1022_:
{
if (v___y_1023_ == 0)
{
lean_dec_ref_known(v___x_1020_, 1);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
goto v___jp_900_;
}
else
{
v___y_904_ = v___x_1020_;
goto v___jp_903_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v___x_891_);
lean_dec_ref(v___f_890_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_1026_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1010_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1010_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v___x_891_);
lean_dec_ref(v___f_890_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_1034_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1005_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1005_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1002_);
lean_dec(v___x_891_);
lean_dec_ref(v___f_890_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_1042_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1003_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1003_);
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
lean_dec(v___x_891_);
lean_dec_ref(v___f_890_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_1050_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1001_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1001_);
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
v___jp_900_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
v___jp_903_:
{
if (lean_obj_tag(v___y_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___y_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___y_904_, 1);
if (lean_obj_tag(v_a_905_) == 0)
{
lean_dec(v___x_888_);
lean_dec(v___x_886_);
goto v___jp_900_;
}
else
{
lean_object* v_val_906_; lean_object* v_fst_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_990_; 
v_val_906_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_a_905_, 1);
v_fst_907_ = lean_ctor_get(v_val_906_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_val_906_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_val_906_, 1);
lean_dec(v_unused_991_);
v___x_909_ = v_val_906_;
v_isShared_910_ = v_isSharedCheck_990_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_fst_907_);
lean_dec(v_val_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_990_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
if (lean_obj_tag(v_fst_907_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = l_Lean_MessageData_ofSyntax(v___x_888_);
v___x_912_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 7);
lean_ctor_set(v___x_909_, 1, v___x_912_);
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_920_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = l_Lean_MessageData_ofSyntax(v___x_886_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_889_, v___x_918_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_919_;
}
}
else
{
lean_object* v_tail_921_; 
v_tail_921_ = lean_ctor_get(v_fst_907_, 1);
if (lean_obj_tag(v_tail_921_) == 0)
{
lean_object* v_head_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_968_; 
v_head_922_ = lean_ctor_get(v_fst_907_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_fst_907_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_fst_907_, 1);
lean_dec(v_unused_969_);
v___x_924_ = v_fst_907_;
v_isShared_925_ = v_isSharedCheck_968_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_head_922_);
lean_dec(v_fst_907_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_968_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_MVarId_getType(v_head_922_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_889_, v_a_927_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_fst_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v_fst_930_ = lean_ctor_get(v_a_929_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_a_929_, 1);
lean_dec(v_unused_951_);
v___x_932_ = v_a_929_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_fst_930_);
lean_dec(v_a_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_934_ = l_Lean_indentExpr(v_fst_930_);
v___x_935_ = l_Lean_MessageData_ofSyntax(v___x_888_);
v___x_936_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 7);
lean_ctor_set(v___x_932_, 1, v___x_936_);
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_949_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_939_ = l_Lean_MessageData_ofSyntax(v___x_886_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 7);
lean_ctor_set(v___x_924_, 1, v___x_939_);
lean_ctor_set(v___x_924_, 0, v___x_938_);
v___x_941_ = v___x_924_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_939_);
v___x_941_ = v_reuseFailAlloc_948_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 7);
lean_ctor_set(v___x_909_, 1, v___x_942_);
lean_ctor_set(v___x_909_, 0, v___x_941_);
v___x_944_ = v___x_909_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_942_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_934_);
v___x_946_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_889_, v___x_945_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_924_);
lean_del_object(v___x_909_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_952_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_928_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_928_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_del_object(v___x_924_);
lean_del_object(v___x_909_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_960_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_926_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_926_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = l_Lean_MessageData_ofSyntax(v___x_888_);
v___x_971_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 7);
lean_ctor_set(v___x_909_, 1, v___x_971_);
lean_ctor_set(v___x_909_, 0, v___x_970_);
v___x_973_ = v___x_909_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_989_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = l_Lean_MessageData_ofSyntax(v___x_886_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_889_, v___x_977_, v_fst_907_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_889_, v_a_979_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_978_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
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
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___x_888_);
lean_dec(v___x_886_);
v_a_992_ = lean_ctor_get(v___y_904_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___y_904_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___y_904_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___y_904_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* v___x_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v_stx_1061_, lean_object* v___f_1062_, lean_object* v___x_1063_, lean_object* v___vars_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_7170__boxed_1072_; lean_object* v_res_1073_; 
v___x_7170__boxed_1072_ = lean_unbox(v___x_1059_);
v_res_1073_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(v___x_1058_, v___x_7170__boxed_1072_, v___x_1060_, v_stx_1061_, v___f_1062_, v___x_1063_, v___vars_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v___vars_1064_);
lean_dec(v_stx_1061_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* v_stx_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
lean_inc(v_stx_1079_);
v___x_1084_ = l_Lean_Syntax_isOfKind(v_stx_1079_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_stx_1079_);
v___x_1085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v_env_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1086_ = lean_st_ref_get(v_a_1081_);
v_env_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_env_1087_);
lean_dec(v___x_1086_);
v___f_1088_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = l_Lean_Syntax_getArg(v_stx_1079_, v___x_1089_);
v___x_1091_ = lean_unsigned_to_nat(3u);
v___x_1092_ = l_Lean_Syntax_getArg(v_stx_1079_, v___x_1091_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_box(v___x_1084_);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1095_, 0, v___x_1090_);
lean_closure_set(v___f_1095_, 1, v___x_1094_);
lean_closure_set(v___f_1095_, 2, v___x_1092_);
lean_closure_set(v___f_1095_, 3, v_stx_1079_);
lean_closure_set(v___f_1095_, 4, v___f_1088_);
lean_closure_set(v___f_1095_, 5, v___x_1093_);
v___x_1096_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, v___f_1095_);
v___x_1097_ = l_Lean_Environment_unlockAsync(v_env_1087_);
v___x_1098_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_1097_, v___x_1096_, v_a_1080_, v_a_1081_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(lean_object* v_stx_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* v_stx_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_1104_, v_x_1105_, v_x_1106_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* v_stx_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_1115_, v_x_1116_, v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_stx_1115_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1133_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1134_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1135_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed), 4, 0);
v___x_1137_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1133_, v___x_1134_, v___x_1135_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1167_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6));
v___x_1168_ = l_Lean_addBuiltinDeclarationRanges(v___x_1166_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
return v_res_1170_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Array_mkArray0(lean_box(0));
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* v_stx_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
lean_inc(v_stx_1196_);
v___x_1200_ = l_Lean_Syntax_isOfKind(v_stx_1196_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec(v_stx_1196_);
v___x_1201_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1198_);
return v___x_1201_;
}
else
{
lean_object* v_ref_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_ref_1202_ = lean_ctor_get(v_a_1197_, 5);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = l_Lean_Syntax_getArg(v_stx_1196_, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(3u);
v___x_1206_ = l_Lean_Syntax_getArg(v_stx_1196_, v___x_1205_);
lean_dec(v_stx_1196_);
v___x_1207_ = 0;
v___x_1208_ = l_Lean_SourceInfo_fromRef(v_ref_1202_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_1210_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2));
lean_inc_n(v___x_1208_, 7);
v___x_1211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1208_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3));
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1208_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1217_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1208_);
lean_ctor_set(v___x_1218_, 1, v___x_1216_);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1220_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1221_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1208_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
lean_ctor_set(v___x_1222_, 2, v___x_1221_);
lean_inc_ref_n(v___x_1222_, 4);
v___x_1223_ = l_Lean_Syntax_node1(v___x_1208_, v___x_1219_, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_node6(v___x_1208_, v___x_1217_, v___x_1218_, v___x_1223_, v___x_1222_, v___x_1222_, v___x_1222_, v___x_1222_);
v___x_1225_ = l_Lean_Syntax_node6(v___x_1208_, v___x_1209_, v___x_1211_, v___x_1204_, v___x_1213_, v___x_1206_, v___x_1215_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_a_1198_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* v_stx_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_CheckTactic_expandCheckSimp(v_stx_1227_, v_a_1228_, v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1238_ = l_Lean_Elab_macroAttribute;
v___x_1239_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1241_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
v___x_1242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1238_, v___x_1239_, v___x_1240_, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6));
v___x_1273_ = l_Lean_addBuiltinDeclarationRanges(v___x_1271_, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* v_stx_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
lean_inc(v_stx_1282_);
v___x_1286_ = l_Lean_Syntax_isOfKind(v_stx_1282_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_stx_1282_);
v___x_1287_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1284_);
return v___x_1287_;
}
else
{
lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_ref_1288_ = lean_ctor_get(v_a_1283_, 5);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = l_Lean_Syntax_getArg(v_stx_1282_, v___x_1289_);
lean_dec(v_stx_1282_);
v___x_1291_ = 0;
v___x_1292_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1294_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2));
lean_inc_n(v___x_1292_, 6);
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1292_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1292_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1299_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1292_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
v___x_1301_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1302_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1303_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1292_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1303_);
lean_inc_ref_n(v___x_1304_, 4);
v___x_1305_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1301_, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_node6(v___x_1292_, v___x_1299_, v___x_1300_, v___x_1305_, v___x_1304_, v___x_1304_, v___x_1304_, v___x_1304_);
v___x_1307_ = l_Lean_Syntax_node4(v___x_1292_, v___x_1293_, v___x_1295_, v___x_1290_, v___x_1297_, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_a_1284_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* v_stx_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(v_stx_1309_, v_a_1310_, v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1320_ = l_Lean_Elab_macroAttribute;
v___x_1321_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1323_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
v___x_1324_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1320_, v___x_1321_, v___x_1322_, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1354_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6));
v___x_1355_ = l_Lean_addBuiltinDeclarationRanges(v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
return v_res_1357_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CheckTactic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_CheckTactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

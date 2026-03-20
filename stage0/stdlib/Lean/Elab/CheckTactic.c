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
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " produced multiple goals, but is expected to reduce to "};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11;
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
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CheckTactic"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value;
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabCheckTactic"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 72, 15, 247, 239, 21, 78, 147)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(95) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(95) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "elabCheckTacticFailure"};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 111, 187, 142, 78, 109, 254, 147)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(73) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expandCheckSimp"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 31, 125, 199, 240, 147, 190, 74)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expandCheckSimpFailure"};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 138, 121, 117, 47, 212, 130, 79)}};
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 74, 202, 176, 97, 48, 121, 220)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(83) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object*);
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
lean_dec_ref(v___x_84_);
if (lean_obj_tag(v_val_86_) == 1)
{
uint8_t v_v_87_; 
v_v_87_ = lean_ctor_get_uint8(v_val_86_, 0);
lean_dec_ref(v_val_86_);
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
lean_inc(v_macroStack_141_);
lean_dec_ref(v___y_131_);
lean_inc(v_macroStack_141_);
v___x_142_ = l_Lean_Elab_getBetterRef(v_ref_138_, v_macroStack_141_);
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
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object* v_ref_162_, lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_fileName_171_; lean_object* v_fileMap_172_; lean_object* v_options_173_; lean_object* v_currRecDepth_174_; lean_object* v_maxRecDepth_175_; lean_object* v_ref_176_; lean_object* v_currNamespace_177_; lean_object* v_openDecls_178_; lean_object* v_initHeartbeats_179_; lean_object* v_maxHeartbeats_180_; lean_object* v_quotContext_181_; lean_object* v_currMacroScope_182_; uint8_t v_diag_183_; lean_object* v_cancelTk_x3f_184_; uint8_t v_suppressElabErrors_185_; lean_object* v_inheritedTraceOptions_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
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
v_isSharedCheck_195_ = !lean_is_exclusive(v___y_168_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v___y_168_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_inheritedTraceOptions_186_);
lean_inc(v_cancelTk_x3f_184_);
lean_inc(v_currMacroScope_182_);
lean_inc(v_quotContext_181_);
lean_inc(v_maxHeartbeats_180_);
lean_inc(v_initHeartbeats_179_);
lean_inc(v_openDecls_178_);
lean_inc(v_currNamespace_177_);
lean_inc(v_ref_176_);
lean_inc(v_maxRecDepth_175_);
lean_inc(v_currRecDepth_174_);
lean_inc(v_options_173_);
lean_inc(v_fileMap_172_);
lean_inc(v_fileName_171_);
lean_dec(v___y_168_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_ref_190_; lean_object* v___x_192_; 
v_ref_190_ = l_Lean_replaceRef(v_ref_162_, v_ref_176_);
lean_dec(v_ref_176_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 5, v_ref_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_fileName_171_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_fileMap_172_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_options_173_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_currRecDepth_174_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_maxRecDepth_175_);
lean_ctor_set(v_reuseFailAlloc_194_, 5, v_ref_190_);
lean_ctor_set(v_reuseFailAlloc_194_, 6, v_currNamespace_177_);
lean_ctor_set(v_reuseFailAlloc_194_, 7, v_openDecls_178_);
lean_ctor_set(v_reuseFailAlloc_194_, 8, v_initHeartbeats_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 9, v_maxHeartbeats_180_);
lean_ctor_set(v_reuseFailAlloc_194_, 10, v_quotContext_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 11, v_currMacroScope_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 12, v_cancelTk_x3f_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 13, v_inheritedTraceOptions_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*14, v_diag_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*14 + 1, v_suppressElabErrors_185_);
v___x_192_ = v_reuseFailAlloc_194_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___x_192_, v___y_169_);
lean_dec_ref(v___x_192_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(lean_object* v_ref_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_196_, v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec(v_ref_196_);
return v_res_205_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static uint64_t _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9(void){
_start:
{
uint8_t v___x_220_; uint64_t v___x_221_; 
v___x_220_ = 2;
v___x_221_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* v___x_225_, uint8_t v___x_226_, lean_object* v___x_227_, lean_object* v___f_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v_stx_231_, lean_object* v___vars_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v___x_243_ = lean_box(0);
v___x_244_ = lean_box(v___x_226_);
v___x_245_ = lean_box(v___x_226_);
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_246_, 0, v___x_225_);
lean_closure_set(v___x_246_, 1, v___x_243_);
lean_closure_set(v___x_246_, 2, v___x_244_);
lean_closure_set(v___x_246_, 3, v___x_245_);
v___x_247_ = 1;
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
v___x_248_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_246_, v___x_247_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_248_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v_a_249_);
v___x_250_ = lean_infer_type(v_a_249_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
lean_inc(v_a_251_);
v___x_252_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_249_, v_a_251_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_253_);
v___x_255_ = 0;
v___x_256_ = lean_box(0);
lean_inc_ref(v___y_235_);
v___x_257_ = l_Lean_Meta_mkFreshExprMVar(v___x_254_, v___x_255_, v___x_256_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_251_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
v___x_260_ = l_Lean_Elab_Term_elabTerm(v___x_227_, v___x_259_, v___x_226_, v___x_226_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_260_);
v___x_262_ = l_Lean_Expr_mvarId_x21(v_a_258_);
lean_dec(v_a_258_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_box(1);
v___x_265_ = 0;
v___x_266_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_267_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_267_, 0, v___x_243_);
lean_ctor_set(v___x_267_, 1, v___x_263_);
lean_ctor_set(v___x_267_, 2, v___x_243_);
lean_ctor_set(v___x_267_, 3, v___f_228_);
lean_ctor_set(v___x_267_, 4, v___x_264_);
lean_ctor_set(v___x_267_, 5, v___x_264_);
lean_ctor_set(v___x_267_, 6, v___x_243_);
lean_ctor_set(v___x_267_, 7, v___x_266_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8, v___x_226_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 1, v___x_226_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 2, v___x_226_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 3, v___x_226_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 4, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 5, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 6, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 7, v___x_226_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 8, v___x_265_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*8 + 9, v___x_226_);
v___x_268_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_268_, 0, v___x_229_);
lean_ctor_set(v___x_268_, 1, v___x_264_);
lean_ctor_set(v___x_268_, 2, v___x_263_);
lean_ctor_set(v___x_268_, 3, v___x_263_);
lean_ctor_set(v___x_268_, 4, v___x_263_);
lean_ctor_set(v___x_268_, 5, v___x_264_);
lean_ctor_set(v___x_268_, 6, v___x_263_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___x_230_);
v___x_269_ = l_Lean_Elab_runTactic(v___x_262_, v___x_230_, v___x_267_, v___x_268_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_fst_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_426_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref(v___x_269_);
v_fst_271_ = lean_ctor_get(v_a_270_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_a_270_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_a_270_, 1);
lean_dec(v_unused_427_);
v___x_273_ = v_a_270_;
v_isShared_274_ = v_isSharedCheck_426_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_fst_271_);
lean_dec(v_a_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_426_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
if (lean_obj_tag(v_fst_271_) == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = l_Lean_MessageData_ofSyntax(v___x_230_);
v___x_276_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 7);
lean_ctor_set(v___x_273_, 1, v___x_276_);
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_284_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_279_ = l_Lean_indentExpr(v_a_261_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_231_, v___x_282_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
return v___x_283_;
}
}
else
{
lean_object* v_tail_285_; 
v_tail_285_ = lean_ctor_get(v_fst_271_, 1);
if (lean_obj_tag(v_tail_285_) == 0)
{
lean_object* v_head_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_273_);
lean_dec(v___x_230_);
v_head_286_ = lean_ctor_get(v_fst_271_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_fst_271_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_fst_271_, 1);
lean_dec(v_unused_407_);
v___x_288_ = v_fst_271_;
v_isShared_289_ = v_isSharedCheck_406_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_head_286_);
lean_dec(v_fst_271_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_406_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_MVarId_getType(v_head_286_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref(v___x_290_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
v___x_292_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_231_, v_a_291_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_fst_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_388_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v___x_292_);
v_fst_294_ = lean_ctor_get(v_a_293_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v_a_293_, 1);
lean_dec(v_unused_389_);
v___x_296_ = v_a_293_;
v_isShared_297_ = v_isSharedCheck_388_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_fst_294_);
lean_dec(v_a_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_388_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v_a_299_; lean_object* v___x_330_; uint8_t v_foApprox_331_; uint8_t v_ctxApprox_332_; uint8_t v_quasiPatternApprox_333_; uint8_t v_constApprox_334_; uint8_t v_isDefEqStuckEx_335_; uint8_t v_unificationHints_336_; uint8_t v_proofIrrelevance_337_; uint8_t v_assignSyntheticOpaque_338_; uint8_t v_offsetCnstrs_339_; uint8_t v_etaStruct_340_; uint8_t v_univApprox_341_; uint8_t v_iota_342_; uint8_t v_beta_343_; uint8_t v_proj_344_; uint8_t v_zeta_345_; uint8_t v_zetaDelta_346_; uint8_t v_zetaUnused_347_; uint8_t v_zetaHave_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_387_; 
v___x_330_ = l_Lean_Meta_Context_config(v___y_235_);
v_foApprox_331_ = lean_ctor_get_uint8(v___x_330_, 0);
v_ctxApprox_332_ = lean_ctor_get_uint8(v___x_330_, 1);
v_quasiPatternApprox_333_ = lean_ctor_get_uint8(v___x_330_, 2);
v_constApprox_334_ = lean_ctor_get_uint8(v___x_330_, 3);
v_isDefEqStuckEx_335_ = lean_ctor_get_uint8(v___x_330_, 4);
v_unificationHints_336_ = lean_ctor_get_uint8(v___x_330_, 5);
v_proofIrrelevance_337_ = lean_ctor_get_uint8(v___x_330_, 6);
v_assignSyntheticOpaque_338_ = lean_ctor_get_uint8(v___x_330_, 7);
v_offsetCnstrs_339_ = lean_ctor_get_uint8(v___x_330_, 8);
v_etaStruct_340_ = lean_ctor_get_uint8(v___x_330_, 10);
v_univApprox_341_ = lean_ctor_get_uint8(v___x_330_, 11);
v_iota_342_ = lean_ctor_get_uint8(v___x_330_, 12);
v_beta_343_ = lean_ctor_get_uint8(v___x_330_, 13);
v_proj_344_ = lean_ctor_get_uint8(v___x_330_, 14);
v_zeta_345_ = lean_ctor_get_uint8(v___x_330_, 15);
v_zetaDelta_346_ = lean_ctor_get_uint8(v___x_330_, 16);
v_zetaUnused_347_ = lean_ctor_get_uint8(v___x_330_, 17);
v_zetaHave_348_ = lean_ctor_get_uint8(v___x_330_, 18);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_387_ == 0)
{
v___x_350_ = v___x_330_;
v_isShared_351_ = v_isSharedCheck_387_;
goto v_resetjp_349_;
}
else
{
lean_dec(v___x_330_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_387_;
goto v_resetjp_349_;
}
v___jp_298_:
{
if (v_a_299_ == 0)
{
if (v___x_226_ == 0)
{
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_288_);
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
goto v___jp_240_;
}
else
{
lean_object* v___x_300_; 
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
v___x_300_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_294_, v_a_261_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_321_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
v_fst_302_ = lean_ctor_get(v_a_301_, 0);
v_snd_303_ = lean_ctor_get(v_a_301_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_301_);
if (v_isSharedCheck_321_ == 0)
{
v___x_305_ = v_a_301_;
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_snd_303_);
lean_inc(v_fst_302_);
lean_dec(v_a_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6);
v___x_308_ = l_Lean_indentExpr(v_fst_302_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 7);
lean_ctor_set(v___x_305_, 1, v___x_308_);
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_320_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 7);
lean_ctor_set(v___x_296_, 1, v___x_311_);
lean_ctor_set(v___x_296_, 0, v___x_310_);
v___x_313_ = v___x_296_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_319_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_indentExpr(v_snd_303_);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 7);
lean_ctor_set(v___x_288_, 1, v___x_314_);
lean_ctor_set(v___x_288_, 0, v___x_313_);
v___x_316_ = v___x_288_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_231_, v___x_316_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_296_);
lean_del_object(v___x_288_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
v_a_322_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_300_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_300_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_288_);
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
goto v___jp_240_;
}
}
v_resetjp_349_:
{
uint8_t v_trackZetaDelta_352_; lean_object* v_zetaDeltaSet_353_; lean_object* v_lctx_354_; lean_object* v_localInstances_355_; lean_object* v_defEqCtx_x3f_356_; lean_object* v_synthPendingDepth_357_; lean_object* v_canUnfold_x3f_358_; uint8_t v_univApprox_359_; uint8_t v_inTypeClassResolution_360_; uint8_t v_cacheInferType_361_; uint8_t v___x_362_; lean_object* v_config_364_; 
v_trackZetaDelta_352_ = lean_ctor_get_uint8(v___y_235_, sizeof(void*)*7);
v_zetaDeltaSet_353_ = lean_ctor_get(v___y_235_, 1);
v_lctx_354_ = lean_ctor_get(v___y_235_, 2);
v_localInstances_355_ = lean_ctor_get(v___y_235_, 3);
v_defEqCtx_x3f_356_ = lean_ctor_get(v___y_235_, 4);
v_synthPendingDepth_357_ = lean_ctor_get(v___y_235_, 5);
v_canUnfold_x3f_358_ = lean_ctor_get(v___y_235_, 6);
v_univApprox_359_ = lean_ctor_get_uint8(v___y_235_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_360_ = lean_ctor_get_uint8(v___y_235_, sizeof(void*)*7 + 2);
v_cacheInferType_361_ = lean_ctor_get_uint8(v___y_235_, sizeof(void*)*7 + 3);
v___x_362_ = 2;
if (v_isShared_351_ == 0)
{
v_config_364_ = v___x_350_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 0, v_foApprox_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 1, v_ctxApprox_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 2, v_quasiPatternApprox_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 3, v_constApprox_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 4, v_isDefEqStuckEx_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 5, v_unificationHints_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 6, v_proofIrrelevance_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 7, v_assignSyntheticOpaque_338_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 8, v_offsetCnstrs_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 10, v_etaStruct_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 11, v_univApprox_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 12, v_iota_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 13, v_beta_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 14, v_proj_344_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 15, v_zeta_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 16, v_zetaDelta_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 17, v_zetaUnused_347_);
lean_ctor_set_uint8(v_reuseFailAlloc_386_, 18, v_zetaHave_348_);
v_config_364_ = v_reuseFailAlloc_386_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v_key_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_ctor_set_uint8(v_config_364_, 9, v___x_362_);
v___x_365_ = l_Lean_Meta_Context_configKey(v___y_235_);
v___x_366_ = 2ULL;
v___x_367_ = lean_uint64_shift_right(v___x_365_, v___x_366_);
v___x_368_ = lean_uint64_shift_left(v___x_367_, v___x_366_);
v___x_369_ = lean_uint64_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9);
v_key_370_ = lean_uint64_lor(v___x_368_, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_371_, 0, v_config_364_);
lean_ctor_set_uint64(v___x_371_, sizeof(void*)*1, v_key_370_);
lean_inc(v_canUnfold_x3f_358_);
lean_inc(v_synthPendingDepth_357_);
lean_inc(v_defEqCtx_x3f_356_);
lean_inc_ref(v_localInstances_355_);
lean_inc_ref(v_lctx_354_);
lean_inc(v_zetaDeltaSet_353_);
v___x_372_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_zetaDeltaSet_353_);
lean_ctor_set(v___x_372_, 2, v_lctx_354_);
lean_ctor_set(v___x_372_, 3, v_localInstances_355_);
lean_ctor_set(v___x_372_, 4, v_defEqCtx_x3f_356_);
lean_ctor_set(v___x_372_, 5, v_synthPendingDepth_357_);
lean_ctor_set(v___x_372_, 6, v_canUnfold_x3f_358_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*7, v_trackZetaDelta_352_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*7 + 1, v_univApprox_359_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*7 + 2, v_inTypeClassResolution_360_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*7 + 3, v_cacheInferType_361_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc(v_a_261_);
lean_inc(v_fst_294_);
v___x_373_ = l_Lean_Meta_isExprDefEq(v_fst_294_, v_a_261_, v___x_372_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; uint8_t v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
v___x_375_ = lean_unbox(v_a_374_);
lean_dec(v_a_374_);
v_a_299_ = v___x_375_;
goto v___jp_298_;
}
else
{
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_376_; uint8_t v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_373_);
v___x_377_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
v_a_299_ = v___x_377_;
goto v___jp_298_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_del_object(v___x_296_);
lean_dec(v_fst_294_);
lean_del_object(v___x_288_);
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
v_a_378_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_373_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_373_);
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
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_del_object(v___x_288_);
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
v_a_390_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_292_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_292_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_del_object(v___x_288_);
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
v_a_398_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_290_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_290_);
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
}
else
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v_fst_271_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_424_ = lean_ctor_get(v_fst_271_, 1);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_fst_271_, 0);
lean_dec(v_unused_425_);
v___x_409_ = v_fst_271_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_fst_271_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = l_Lean_MessageData_ofSyntax(v___x_230_);
v___x_412_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 7);
lean_ctor_set(v___x_409_, 1, v___x_412_);
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_422_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_indentExpr(v_a_261_);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 7);
lean_ctor_set(v___x_273_, 1, v___x_415_);
lean_ctor_set(v___x_273_, 0, v___x_414_);
v___x_417_ = v___x_273_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_231_, v___x_419_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
return v___x_420_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_a_261_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
v_a_428_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_269_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_269_);
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
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_258_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec_ref(v___f_228_);
v_a_436_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_260_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_260_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_a_251_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec_ref(v___f_228_);
lean_dec(v___x_227_);
v_a_444_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_257_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_257_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_a_251_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec_ref(v___f_228_);
lean_dec(v___x_227_);
v_a_452_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_252_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_252_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_249_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec_ref(v___f_228_);
lean_dec(v___x_227_);
v_a_460_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_250_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_250_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___x_230_);
lean_dec(v___x_229_);
lean_dec_ref(v___f_228_);
lean_dec(v___x_227_);
v_a_468_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_248_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_248_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
v___jp_240_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___f_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v_stx_482_, lean_object* v___vars_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v___x_12092__boxed_491_; lean_object* v_res_492_; 
v___x_12092__boxed_491_ = lean_unbox(v___x_477_);
v_res_492_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(v___x_476_, v___x_12092__boxed_491_, v___x_478_, v___f_479_, v___x_480_, v___x_481_, v_stx_482_, v___vars_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec_ref(v___vars_483_);
lean_dec(v_stx_482_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(lean_object* v_env_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_messages_497_; lean_object* v_scopes_498_; lean_object* v_usedQuotCtxts_499_; lean_object* v_nextMacroScope_500_; lean_object* v_maxRecDepth_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_infoState_504_; lean_object* v_traceState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v___x_496_ = lean_st_ref_take(v___y_494_);
v_messages_497_ = lean_ctor_get(v___x_496_, 1);
v_scopes_498_ = lean_ctor_get(v___x_496_, 2);
v_usedQuotCtxts_499_ = lean_ctor_get(v___x_496_, 3);
v_nextMacroScope_500_ = lean_ctor_get(v___x_496_, 4);
v_maxRecDepth_501_ = lean_ctor_get(v___x_496_, 5);
v_ngen_502_ = lean_ctor_get(v___x_496_, 6);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_496_, 7);
v_infoState_504_ = lean_ctor_get(v___x_496_, 8);
v_traceState_505_ = lean_ctor_get(v___x_496_, 9);
v_snapshotTasks_506_ = lean_ctor_get(v___x_496_, 10);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_496_, 0);
lean_dec(v_unused_517_);
v___x_508_ = v___x_496_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_traceState_505_);
lean_inc(v_infoState_504_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_maxRecDepth_501_);
lean_inc(v_nextMacroScope_500_);
lean_inc(v_usedQuotCtxts_499_);
lean_inc(v_scopes_498_);
lean_inc(v_messages_497_);
lean_dec(v___x_496_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_env_493_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_env_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_messages_497_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_scopes_498_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_usedQuotCtxts_499_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_nextMacroScope_500_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_maxRecDepth_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_infoState_504_);
lean_ctor_set(v_reuseFailAlloc_515_, 9, v_traceState_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 10, v_snapshotTasks_506_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_st_ref_set(v___y_494_, v___x_511_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(lean_object* v_env_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_518_, v___y_519_);
lean_dec(v___y_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(lean_object* v_env_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_env_528_; lean_object* v_a_530_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_527_ = lean_st_ref_get(v___y_525_);
v_env_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_528_);
lean_dec(v___x_527_);
v___x_540_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_522_, v___y_525_);
lean_dec_ref(v___x_540_);
lean_inc(v___y_525_);
v___x_541_ = lean_apply_3(v_x_523_, v___y_524_, v___y_525_, lean_box(0));
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
v___x_543_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_528_, v___y_525_);
lean_dec(v___y_525_);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_543_, 0);
lean_dec(v_unused_551_);
v___x_545_ = v___x_543_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_dec(v___x_543_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_a_542_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_542_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_552_);
lean_dec_ref(v___x_541_);
v_a_530_ = v_a_552_;
goto v___jp_529_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v___x_531_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_528_, v___y_525_);
lean_dec(v___y_525_);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v___x_531_, 0);
lean_dec(v_unused_539_);
v___x_533_ = v___x_531_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_dec(v___x_531_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 1);
lean_ctor_set(v___x_533_, 0, v_a_530_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(lean_object* v_env_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_553_, v_x_554_, v___y_555_, v___y_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* v_stx_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
lean_inc(v_stx_567_);
v___x_572_ = l_Lean_Syntax_isOfKind(v_stx_567_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_stx_567_);
v___x_573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v_env_575_; lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_574_ = lean_st_ref_get(v_a_569_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_574_);
v___f_576_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = l_Lean_Syntax_getArg(v_stx_567_, v___x_577_);
v___x_579_ = lean_unsigned_to_nat(3u);
v___x_580_ = l_Lean_Syntax_getArg(v_stx_567_, v___x_579_);
v___x_581_ = lean_unsigned_to_nat(5u);
v___x_582_ = l_Lean_Syntax_getArg(v_stx_567_, v___x_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_box(v___x_572_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 15, 7);
lean_closure_set(v___f_585_, 0, v___x_578_);
lean_closure_set(v___f_585_, 1, v___x_584_);
lean_closure_set(v___f_585_, 2, v___x_580_);
lean_closure_set(v___f_585_, 3, v___f_576_);
lean_closure_set(v___f_585_, 4, v___x_583_);
lean_closure_set(v___f_585_, 5, v___x_582_);
lean_closure_set(v___f_585_, 6, v_stx_567_);
v___x_586_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_586_, 0, lean_box(0));
lean_closure_set(v___x_586_, 1, v___f_585_);
v___x_587_ = l_Lean_Environment_unlockAsync(v_env_575_);
v___x_588_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_587_, v___x_586_, v_a_568_, v_a_569_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(lean_object* v_stx_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_589_, v_a_590_, v_a_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object* v_00_u03b1_594_, lean_object* v_ref_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_595_, v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object* v_00_u03b1_605_, lean_object* v_ref_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(v_00_u03b1_605_, v_ref_606_, v_msg_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v_ref_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(lean_object* v_env_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_616_, v___y_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(lean_object* v_env_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_object* v_00_u03b1_626_, lean_object* v_env_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_627_, v_x_628_, v___y_629_, v___y_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(lean_object* v_00_u03b1_633_, lean_object* v_env_634_, lean_object* v_x_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(v_00_u03b1_633_, v_env_634_, v_x_635_, v___y_636_, v___y_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object* v_00_u03b1_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object* v_00_u03b1_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(v_00_u03b1_650_, v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(lean_object* v_msgData_660_, lean_object* v_macroStack_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_660_, v_macroStack_661_, v___y_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_670_, lean_object* v_macroStack_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_670_, v_macroStack_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_690_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_691_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_692_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___boxed), 4, 0);
v___x_693_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_689_, v___x_690_, v___x_691_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_723_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6));
v___x_724_ = l_Lean_addBuiltinDeclarationRanges(v___x_722_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(lean_object* v_a_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(lean_object* v_a_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_object* v_00_u03b1_745_, lean_object* v_a_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(lean_object* v_00_u03b1_755_, lean_object* v_a_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(v_00_u03b1_755_, v_a_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Elab_runTactic(v___x_765_, v___x_766_, v___x_767_, v___x_768_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_a_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_776_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_776_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(v___x_794_, v___x_795_, v___x_796_, v___x_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* v_stx_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_814_; 
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_x_807_);
return v___x_814_;
}
else
{
lean_object* v_head_815_; lean_object* v_tail_816_; lean_object* v___x_817_; 
v_head_815_ = lean_ctor_get(v_x_808_, 0);
lean_inc(v_head_815_);
v_tail_816_ = lean_ctor_get(v_x_808_, 1);
lean_inc(v_tail_816_);
lean_dec_ref(v_x_808_);
v___x_817_ = l_Lean_MVarId_getType(v_head_815_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_817_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_819_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_806_, v_a_818_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_fst_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_830_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
v_fst_821_ = lean_ctor_get(v_a_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v_a_820_, 1);
lean_dec(v_unused_831_);
v___x_823_ = v_a_820_;
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_fst_821_);
lean_dec(v_a_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_indentExpr(v_fst_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 7);
lean_ctor_set(v___x_823_, 1, v___x_825_);
lean_ctor_set(v___x_823_, 0, v_x_807_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_x_807_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v_x_807_ = v___x_827_;
v_x_808_ = v_tail_816_;
goto _start;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_tail_816_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_x_807_);
v_a_832_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_819_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_819_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_tail_816_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_x_807_);
v_a_840_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_817_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_817_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* v_stx_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_848_, v_x_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v_stx_848_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* v_stx_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_867_; 
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_x_858_);
return v___x_867_;
}
else
{
lean_object* v_head_868_; lean_object* v_tail_869_; lean_object* v___x_870_; 
v_head_868_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_head_868_);
v_tail_869_ = lean_ctor_get(v_x_859_, 1);
lean_inc(v_tail_869_);
lean_dec_ref(v_x_859_);
v___x_870_ = l_Lean_MVarId_getType(v_head_868_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
v___x_872_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_857_, v_a_871_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v_fst_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_883_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
v_fst_874_ = lean_ctor_get(v_a_873_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_a_873_, 1);
lean_dec(v_unused_884_);
v___x_876_ = v_a_873_;
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_fst_874_);
lean_dec(v_a_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_indentExpr(v_fst_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 7);
lean_ctor_set(v___x_876_, 1, v___x_878_);
lean_ctor_set(v___x_876_, 0, v_x_858_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_x_858_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_857_, v___x_880_, v_tail_869_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_881_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_tail_869_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_x_858_);
v_a_885_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_872_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_872_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_tail_869_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_x_858_);
v_a_893_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_870_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_870_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* v_stx_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_901_, v_x_902_, v_x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v_stx_901_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* v___x_924_, uint8_t v___x_925_, lean_object* v___x_926_, lean_object* v_stx_927_, lean_object* v___f_928_, lean_object* v___x_929_, lean_object* v___vars_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___y_942_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___x_924_);
v___x_1039_ = l_Lean_Elab_Term_elabTerm(v___x_924_, v___x_1038_, v___x_925_, v___x_925_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v_a_1040_);
v___x_1041_ = lean_infer_type(v_a_1040_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_1040_, v_a_1042_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1044_);
v___x_1046_ = 0;
v___x_1047_ = lean_box(0);
lean_inc_ref(v___y_933_);
v___x_1048_ = l_Lean_Meta_mkFreshExprMVar(v___x_1045_, v___x_1046_, v___x_1047_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = l_Lean_Expr_mvarId_x21(v_a_1049_);
lean_dec(v_a_1049_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_box(1);
v___x_1053_ = 0;
v___x_1054_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_1055_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1055_, 0, v___x_1038_);
lean_ctor_set(v___x_1055_, 1, v___x_1051_);
lean_ctor_set(v___x_1055_, 2, v___x_1038_);
lean_ctor_set(v___x_1055_, 3, v___f_928_);
lean_ctor_set(v___x_1055_, 4, v___x_1052_);
lean_ctor_set(v___x_1055_, 5, v___x_1052_);
lean_ctor_set(v___x_1055_, 6, v___x_1038_);
lean_ctor_set(v___x_1055_, 7, v___x_1054_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8, v___x_925_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 1, v___x_925_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 2, v___x_925_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 3, v___x_925_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 4, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 5, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 6, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 7, v___x_925_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 8, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*8 + 9, v___x_925_);
v___x_1056_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1056_, 0, v___x_929_);
lean_ctor_set(v___x_1056_, 1, v___x_1052_);
lean_ctor_set(v___x_1056_, 2, v___x_1051_);
lean_ctor_set(v___x_1056_, 3, v___x_1051_);
lean_ctor_set(v___x_1056_, 4, v___x_1051_);
lean_ctor_set(v___x_1056_, 5, v___x_1052_);
lean_ctor_set(v___x_1056_, 6, v___x_1051_);
lean_inc(v___x_926_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1057_, 0, v___x_1050_);
lean_closure_set(v___f_1057_, 1, v___x_926_);
lean_closure_set(v___f_1057_, 2, v___x_1055_);
lean_closure_set(v___f_1057_, 3, v___x_1056_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
v___x_1058_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_1057_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1058_) == 0)
{
v___y_942_ = v___x_1058_;
goto v___jp_941_;
}
else
{
lean_object* v_a_1059_; uint8_t v___y_1061_; uint8_t v___x_1062_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
v___x_1062_ = l_Lean_Exception_isInterrupt(v_a_1059_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_Exception_isRuntime(v_a_1059_);
v___y_1061_ = v___x_1063_;
goto v___jp_1060_;
}
else
{
lean_dec(v_a_1059_);
v___y_1061_ = v___x_1062_;
goto v___jp_1060_;
}
v___jp_1060_:
{
if (v___y_1061_ == 0)
{
lean_dec_ref(v___x_1058_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
goto v___jp_938_;
}
else
{
v___y_942_ = v___x_1058_;
goto v___jp_941_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_929_);
lean_dec_ref(v___f_928_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_1064_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1048_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1048_);
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
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_929_);
lean_dec_ref(v___f_928_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_1072_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1043_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1043_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1040_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_929_);
lean_dec_ref(v___f_928_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_1080_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1041_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1041_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_929_);
lean_dec_ref(v___f_928_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_1088_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1039_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1039_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_938_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
v___jp_941_:
{
if (lean_obj_tag(v___y_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___y_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v___y_942_);
if (lean_obj_tag(v_a_943_) == 0)
{
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
goto v___jp_938_;
}
else
{
lean_object* v_val_944_; lean_object* v_fst_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1028_; 
v_val_944_ = lean_ctor_get(v_a_943_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v_a_943_);
v_fst_945_ = lean_ctor_get(v_val_944_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_val_944_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_val_944_, 1);
lean_dec(v_unused_1029_);
v___x_947_ = v_val_944_;
v_isShared_948_ = v_isSharedCheck_1028_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_fst_945_);
lean_dec(v_val_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1028_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
if (lean_obj_tag(v_fst_945_) == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = l_Lean_MessageData_ofSyntax(v___x_926_);
v___x_950_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 7);
lean_ctor_set(v___x_947_, 1, v___x_950_);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_958_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_953_ = l_Lean_MessageData_ofSyntax(v___x_924_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_927_, v___x_956_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
return v___x_957_;
}
}
else
{
lean_object* v_tail_959_; 
v_tail_959_ = lean_ctor_get(v_fst_945_, 1);
if (lean_obj_tag(v_tail_959_) == 0)
{
lean_object* v_head_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1006_; 
v_head_960_ = lean_ctor_get(v_fst_945_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_fst_945_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_fst_945_, 1);
lean_dec(v_unused_1007_);
v___x_962_ = v_fst_945_;
v_isShared_963_ = v_isSharedCheck_1006_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_head_960_);
lean_dec(v_fst_945_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1006_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_MVarId_getType(v_head_960_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
v___x_966_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_927_, v_a_965_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v_fst_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_988_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
v_fst_968_ = lean_ctor_get(v_a_967_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_a_967_, 1);
lean_dec(v_unused_989_);
v___x_970_ = v_a_967_;
v_isShared_971_ = v_isSharedCheck_988_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_fst_968_);
lean_dec(v_a_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_988_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_972_ = l_Lean_indentExpr(v_fst_968_);
v___x_973_ = l_Lean_MessageData_ofSyntax(v___x_926_);
v___x_974_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 7);
lean_ctor_set(v___x_970_, 1, v___x_974_);
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_976_ = v___x_970_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_987_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_MessageData_ofSyntax(v___x_924_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 7);
lean_ctor_set(v___x_962_, 1, v___x_977_);
lean_ctor_set(v___x_962_, 0, v___x_976_);
v___x_979_ = v___x_962_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_986_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 7);
lean_ctor_set(v___x_947_, 1, v___x_980_);
lean_ctor_set(v___x_947_, 0, v___x_979_);
v___x_982_ = v___x_947_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_972_);
v___x_984_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_927_, v___x_983_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
return v___x_984_;
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_del_object(v___x_962_);
lean_del_object(v___x_947_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_990_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_966_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_966_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_del_object(v___x_962_);
lean_del_object(v___x_947_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_998_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_964_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_964_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
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
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = l_Lean_MessageData_ofSyntax(v___x_926_);
v___x_1009_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 7);
lean_ctor_set(v___x_947_, 1, v___x_1009_);
lean_ctor_set(v___x_947_, 0, v___x_1008_);
v___x_1011_ = v___x_947_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1012_ = l_Lean_MessageData_ofSyntax(v___x_924_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
v___x_1016_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_927_, v___x_1015_, v_fst_945_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_927_, v_a_1017_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1016_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
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
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_a_1030_ = lean_ctor_get(v___y_942_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___y_942_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___y_942_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___y_942_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v_stx_1099_, lean_object* v___f_1100_, lean_object* v___x_1101_, lean_object* v___vars_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_7651__boxed_1110_; lean_object* v_res_1111_; 
v___x_7651__boxed_1110_ = lean_unbox(v___x_1097_);
v_res_1111_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(v___x_1096_, v___x_7651__boxed_1110_, v___x_1098_, v_stx_1099_, v___f_1100_, v___x_1101_, v___vars_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref(v___vars_1102_);
lean_dec(v_stx_1099_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* v_stx_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
lean_inc(v_stx_1117_);
v___x_1122_ = l_Lean_Syntax_isOfKind(v_stx_1117_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_stx_1117_);
v___x_1123_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v_env_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1124_ = lean_st_ref_get(v_a_1119_);
v_env_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_env_1125_);
lean_dec(v___x_1124_);
v___f_1126_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1127_);
v___x_1129_ = lean_unsigned_to_nat(3u);
v___x_1130_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_box(v___x_1122_);
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1133_, 0, v___x_1128_);
lean_closure_set(v___f_1133_, 1, v___x_1132_);
lean_closure_set(v___f_1133_, 2, v___x_1130_);
lean_closure_set(v___f_1133_, 3, v_stx_1117_);
lean_closure_set(v___f_1133_, 4, v___f_1126_);
lean_closure_set(v___f_1133_, 5, v___x_1131_);
v___x_1134_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_1134_, 0, lean_box(0));
lean_closure_set(v___x_1134_, 1, v___f_1133_);
v___x_1135_ = l_Lean_Environment_unlockAsync(v_env_1125_);
v___x_1136_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_1135_, v___x_1134_, v_a_1118_, v_a_1119_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(lean_object* v_stx_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_1137_, v_a_1138_, v_a_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* v_stx_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_1142_, v_x_1143_, v_x_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* v_stx_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_1153_, v_x_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_stx_1153_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1172_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1173_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1174_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed), 4, 0);
v___x_1175_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1171_, v___x_1172_, v___x_1173_, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1205_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6));
v___x_1206_ = l_Lean_addBuiltinDeclarationRanges(v___x_1204_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12(void){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Array_mkArray0(lean_box(0));
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* v_stx_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
lean_inc(v_stx_1234_);
v___x_1238_ = l_Lean_Syntax_isOfKind(v_stx_1234_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec(v_stx_1234_);
v___x_1239_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1236_);
return v___x_1239_;
}
else
{
lean_object* v_ref_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_ref_1240_ = lean_ctor_get(v_a_1235_, 5);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = l_Lean_Syntax_getArg(v_stx_1234_, v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(3u);
v___x_1244_ = l_Lean_Syntax_getArg(v_stx_1234_, v___x_1243_);
lean_dec(v_stx_1234_);
v___x_1245_ = 0;
v___x_1246_ = l_Lean_SourceInfo_fromRef(v_ref_1240_, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_1248_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2));
lean_inc(v___x_1246_);
v___x_1249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3));
lean_inc(v___x_1246_);
v___x_1251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1246_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
lean_inc(v___x_1246_);
v___x_1253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1246_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1255_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
lean_inc(v___x_1246_);
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1246_);
lean_ctor_set(v___x_1256_, 1, v___x_1254_);
v___x_1257_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1258_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1259_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
lean_inc(v___x_1246_);
v___x_1260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1246_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
lean_inc_ref(v___x_1260_);
lean_inc(v___x_1246_);
v___x_1261_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1257_, v___x_1260_);
lean_inc_ref_n(v___x_1260_, 3);
lean_inc(v___x_1246_);
v___x_1262_ = l_Lean_Syntax_node6(v___x_1246_, v___x_1255_, v___x_1256_, v___x_1261_, v___x_1260_, v___x_1260_, v___x_1260_, v___x_1260_);
v___x_1263_ = l_Lean_Syntax_node6(v___x_1246_, v___x_1247_, v___x_1249_, v___x_1242_, v___x_1251_, v___x_1244_, v___x_1253_, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1236_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* v_stx_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Elab_CheckTactic_expandCheckSimp(v_stx_1265_, v_a_1266_, v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1276_ = l_Lean_Elab_macroAttribute;
v___x_1277_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
v___x_1278_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1279_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
v___x_1280_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1276_, v___x_1277_, v___x_1278_, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1310_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6));
v___x_1311_ = l_Lean_addBuiltinDeclarationRanges(v___x_1309_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* v_stx_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
lean_inc(v_stx_1320_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v_stx_1320_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec(v_stx_1320_);
v___x_1325_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1322_);
return v___x_1325_;
}
else
{
lean_object* v_ref_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_ref_1326_ = lean_ctor_get(v_a_1321_, 5);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = l_Lean_Syntax_getArg(v_stx_1320_, v___x_1327_);
lean_dec(v_stx_1320_);
v___x_1329_ = 0;
v___x_1330_ = l_Lean_SourceInfo_fromRef(v_ref_1326_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1332_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2));
lean_inc(v___x_1330_);
v___x_1333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1330_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
lean_inc(v___x_1330_);
v___x_1335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1330_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1337_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
lean_inc(v___x_1330_);
v___x_1338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1330_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
v___x_1339_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1340_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1341_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
lean_inc(v___x_1330_);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1330_);
lean_ctor_set(v___x_1342_, 1, v___x_1340_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_inc_ref(v___x_1342_);
lean_inc(v___x_1330_);
v___x_1343_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1339_, v___x_1342_);
lean_inc_ref_n(v___x_1342_, 3);
lean_inc(v___x_1330_);
v___x_1344_ = l_Lean_Syntax_node6(v___x_1330_, v___x_1337_, v___x_1338_, v___x_1343_, v___x_1342_, v___x_1342_, v___x_1342_, v___x_1342_);
v___x_1345_ = l_Lean_Syntax_node4(v___x_1330_, v___x_1331_, v___x_1333_, v___x_1328_, v___x_1335_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_a_1322_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* v_stx_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(v_stx_1347_, v_a_1348_, v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1358_ = l_Lean_Elab_macroAttribute;
v___x_1359_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
v___x_1360_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1361_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
v___x_1362_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1358_, v___x_1359_, v___x_1360_, v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1392_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6));
v___x_1393_ = l_Lean_addBuiltinDeclarationRanges(v___x_1391_, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
return v_res_1395_;
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
res = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
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

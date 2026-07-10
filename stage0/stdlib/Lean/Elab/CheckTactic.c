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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* v_options_102_; lean_object* v___x_103_; uint8_t v___x_104_; uint8_t v___x_105_; 
v_options_102_ = lean_ctor_get(v___y_100_, 2);
v___x_103_ = l_Lean_Elab_pp_macroStack;
v___x_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_options_102_, v___x_103_);
v___x_105_ = lean_bool_not(v___x_104_);
if (v___x_105_ == 0)
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
else
{
lean_object* v___x_125_; 
lean_dec(v_macroStack_99_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v_msgData_98_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_126_, lean_object* v_macroStack_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_126_, v_macroStack_127_, v___y_128_);
lean_dec_ref(v___y_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_ref_139_; lean_object* v___x_140_; lean_object* v_a_141_; lean_object* v_macroStack_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_ref_139_ = lean_ctor_get(v___y_136_, 5);
v___x_140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msg_131_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref(v___x_140_);
v_macroStack_142_ = lean_ctor_get(v___y_132_, 1);
v___x_143_ = l_Lean_Elab_getBetterRef(v_ref_139_, v_macroStack_142_);
lean_inc(v_macroStack_142_);
v___x_144_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_a_141_, v_macroStack_142_, v___y_136_);
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_153_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_143_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 1);
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(lean_object* v_ref_163_, lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_fileName_172_; lean_object* v_fileMap_173_; lean_object* v_options_174_; lean_object* v_currRecDepth_175_; lean_object* v_maxRecDepth_176_; lean_object* v_ref_177_; lean_object* v_currNamespace_178_; lean_object* v_openDecls_179_; lean_object* v_initHeartbeats_180_; lean_object* v_maxHeartbeats_181_; lean_object* v_quotContext_182_; lean_object* v_currMacroScope_183_; uint8_t v_diag_184_; lean_object* v_cancelTk_x3f_185_; uint8_t v_suppressElabErrors_186_; lean_object* v_inheritedTraceOptions_187_; lean_object* v_ref_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_fileName_172_ = lean_ctor_get(v___y_169_, 0);
v_fileMap_173_ = lean_ctor_get(v___y_169_, 1);
v_options_174_ = lean_ctor_get(v___y_169_, 2);
v_currRecDepth_175_ = lean_ctor_get(v___y_169_, 3);
v_maxRecDepth_176_ = lean_ctor_get(v___y_169_, 4);
v_ref_177_ = lean_ctor_get(v___y_169_, 5);
v_currNamespace_178_ = lean_ctor_get(v___y_169_, 6);
v_openDecls_179_ = lean_ctor_get(v___y_169_, 7);
v_initHeartbeats_180_ = lean_ctor_get(v___y_169_, 8);
v_maxHeartbeats_181_ = lean_ctor_get(v___y_169_, 9);
v_quotContext_182_ = lean_ctor_get(v___y_169_, 10);
v_currMacroScope_183_ = lean_ctor_get(v___y_169_, 11);
v_diag_184_ = lean_ctor_get_uint8(v___y_169_, sizeof(void*)*14);
v_cancelTk_x3f_185_ = lean_ctor_get(v___y_169_, 12);
v_suppressElabErrors_186_ = lean_ctor_get_uint8(v___y_169_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_187_ = lean_ctor_get(v___y_169_, 13);
v_ref_188_ = l_Lean_replaceRef(v_ref_163_, v_ref_177_);
lean_inc_ref(v_inheritedTraceOptions_187_);
lean_inc(v_cancelTk_x3f_185_);
lean_inc(v_currMacroScope_183_);
lean_inc(v_quotContext_182_);
lean_inc(v_maxHeartbeats_181_);
lean_inc(v_initHeartbeats_180_);
lean_inc(v_openDecls_179_);
lean_inc(v_currNamespace_178_);
lean_inc(v_maxRecDepth_176_);
lean_inc(v_currRecDepth_175_);
lean_inc_ref(v_options_174_);
lean_inc_ref(v_fileMap_173_);
lean_inc_ref(v_fileName_172_);
v___x_189_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_189_, 0, v_fileName_172_);
lean_ctor_set(v___x_189_, 1, v_fileMap_173_);
lean_ctor_set(v___x_189_, 2, v_options_174_);
lean_ctor_set(v___x_189_, 3, v_currRecDepth_175_);
lean_ctor_set(v___x_189_, 4, v_maxRecDepth_176_);
lean_ctor_set(v___x_189_, 5, v_ref_188_);
lean_ctor_set(v___x_189_, 6, v_currNamespace_178_);
lean_ctor_set(v___x_189_, 7, v_openDecls_179_);
lean_ctor_set(v___x_189_, 8, v_initHeartbeats_180_);
lean_ctor_set(v___x_189_, 9, v_maxHeartbeats_181_);
lean_ctor_set(v___x_189_, 10, v_quotContext_182_);
lean_ctor_set(v___x_189_, 11, v_currMacroScope_183_);
lean_ctor_set(v___x_189_, 12, v_cancelTk_x3f_185_);
lean_ctor_set(v___x_189_, 13, v_inheritedTraceOptions_187_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*14, v_diag_184_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*14 + 1, v_suppressElabErrors_186_);
v___x_190_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___x_189_, v___y_170_);
lean_dec_ref_known(v___x_189_, 14);
return v___x_190_;
}
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
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
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
static uint64_t _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9(void){
_start:
{
uint8_t v___x_215_; uint64_t v___x_216_; 
v___x_215_ = 2;
v___x_216_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(lean_object* v___x_220_, uint8_t v___x_221_, lean_object* v___x_222_, lean_object* v___f_223_, lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v_stx_226_, lean_object* v___vars_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_235_ = lean_box(0);
v___x_236_ = lean_box(v___x_221_);
v___x_237_ = lean_box(v___x_221_);
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_238_, 0, v___x_220_);
lean_closure_set(v___x_238_, 1, v___x_235_);
lean_closure_set(v___x_238_, 2, v___x_236_);
lean_closure_set(v___x_238_, 3, v___x_237_);
v___x_239_ = 1;
v___x_240_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_238_, v___x_239_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_n(v_a_241_, 2);
lean_dec_ref_known(v___x_240_, 1);
lean_inc(v___y_233_);
lean_inc_ref(v___y_232_);
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
v___x_242_ = lean_infer_type(v_a_241_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_n(v_a_243_, 2);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_241_, v_a_243_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
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
v___x_249_ = l_Lean_Meta_mkFreshExprMVar(v___x_246_, v___x_247_, v___x_248_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_a_243_);
v___x_252_ = l_Lean_Elab_Term_elabTerm(v___x_222_, v___x_251_, v___x_221_, v___x_221_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
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
lean_ctor_set(v___x_259_, 3, v___f_223_);
lean_ctor_set(v___x_259_, 4, v___x_256_);
lean_ctor_set(v___x_259_, 5, v___x_256_);
lean_ctor_set(v___x_259_, 6, v___x_235_);
lean_ctor_set(v___x_259_, 7, v___x_258_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8, v___x_221_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 1, v___x_221_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 2, v___x_221_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 3, v___x_221_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 4, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 5, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 6, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 7, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 8, v___x_221_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 9, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*8 + 10, v___x_221_);
v___x_260_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_260_, 0, v___x_224_);
lean_ctor_set(v___x_260_, 1, v___x_256_);
lean_ctor_set(v___x_260_, 2, v___x_255_);
lean_ctor_set(v___x_260_, 3, v___x_255_);
lean_ctor_set(v___x_260_, 4, v___x_255_);
lean_ctor_set(v___x_260_, 5, v___x_256_);
lean_ctor_set(v___x_260_, 6, v___x_255_);
lean_inc(v___x_225_);
v___x_261_ = l_Lean_Elab_runTactic(v___x_254_, v___x_225_, v___x_259_, v___x_260_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_fst_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_427_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v_fst_263_ = lean_ctor_get(v_a_262_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v_a_262_, 1);
lean_dec(v_unused_428_);
v___x_265_ = v_a_262_;
v_isShared_266_ = v_isSharedCheck_427_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_fst_263_);
lean_dec(v_a_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_427_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
if (lean_obj_tag(v_fst_263_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_267_ = l_Lean_MessageData_ofSyntax(v___x_225_);
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
v___x_275_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_226_, v___x_274_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_275_;
}
}
else
{
lean_object* v_tail_277_; 
v_tail_277_ = lean_ctor_get(v_fst_263_, 1);
if (lean_obj_tag(v_tail_277_) == 0)
{
lean_object* v_head_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_265_);
lean_dec(v___x_225_);
v_head_278_ = lean_ctor_get(v_fst_263_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_fst_263_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_fst_263_, 1);
lean_dec(v_unused_408_);
v___x_280_ = v_fst_263_;
v_isShared_281_ = v_isSharedCheck_407_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_head_278_);
lean_dec(v_fst_263_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_407_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_MVarId_getType(v_head_278_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_226_, v_a_283_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_390_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_390_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_390_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_390_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_fst_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_388_; 
v_fst_289_ = lean_ctor_get(v_a_285_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v_a_285_, 1);
lean_dec(v_unused_389_);
v___x_291_ = v_a_285_;
v_isShared_292_ = v_isSharedCheck_388_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_fst_289_);
lean_dec(v_a_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_388_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v_a_294_; lean_object* v___x_330_; uint8_t v_foApprox_331_; uint8_t v_ctxApprox_332_; uint8_t v_quasiPatternApprox_333_; uint8_t v_constApprox_334_; uint8_t v_isDefEqStuckEx_335_; uint8_t v_unificationHints_336_; uint8_t v_proofIrrelevance_337_; uint8_t v_assignSyntheticOpaque_338_; uint8_t v_offsetCnstrs_339_; uint8_t v_etaStruct_340_; uint8_t v_univApprox_341_; uint8_t v_iota_342_; uint8_t v_beta_343_; uint8_t v_proj_344_; uint8_t v_zeta_345_; uint8_t v_zetaDelta_346_; uint8_t v_zetaUnused_347_; uint8_t v_zetaHave_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_387_; 
v___x_330_ = l_Lean_Meta_Context_config(v___y_230_);
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
v___jp_293_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_bool_not(v_a_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_del_object(v___x_291_);
lean_dec(v_fst_289_);
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v___x_296_ = lean_box(0);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_296_);
v___x_298_ = v___x_287_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_300_; 
lean_del_object(v___x_287_);
v___x_300_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_fst_289_, v_a_253_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_321_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
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
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_311_);
lean_ctor_set(v___x_291_, 0, v___x_310_);
v___x_313_ = v___x_291_;
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
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 7);
lean_ctor_set(v___x_280_, 1, v___x_314_);
lean_ctor_set(v___x_280_, 0, v___x_313_);
v___x_316_ = v___x_280_;
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
v___x_317_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_226_, v___x_316_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_291_);
lean_del_object(v___x_280_);
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
v_resetjp_349_:
{
uint8_t v_trackZetaDelta_352_; lean_object* v_zetaDeltaSet_353_; lean_object* v_lctx_354_; lean_object* v_localInstances_355_; lean_object* v_defEqCtx_x3f_356_; lean_object* v_synthPendingDepth_357_; lean_object* v_canUnfold_x3f_358_; uint8_t v_univApprox_359_; uint8_t v_inTypeClassResolution_360_; uint8_t v_cacheInferType_361_; uint8_t v___x_362_; lean_object* v_config_364_; 
v_trackZetaDelta_352_ = lean_ctor_get_uint8(v___y_230_, sizeof(void*)*7);
v_zetaDeltaSet_353_ = lean_ctor_get(v___y_230_, 1);
v_lctx_354_ = lean_ctor_get(v___y_230_, 2);
v_localInstances_355_ = lean_ctor_get(v___y_230_, 3);
v_defEqCtx_x3f_356_ = lean_ctor_get(v___y_230_, 4);
v_synthPendingDepth_357_ = lean_ctor_get(v___y_230_, 5);
v_canUnfold_x3f_358_ = lean_ctor_get(v___y_230_, 6);
v_univApprox_359_ = lean_ctor_get_uint8(v___y_230_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_360_ = lean_ctor_get_uint8(v___y_230_, sizeof(void*)*7 + 2);
v_cacheInferType_361_ = lean_ctor_get_uint8(v___y_230_, sizeof(void*)*7 + 3);
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
v___x_365_ = l_Lean_Meta_Context_configKey(v___y_230_);
v___x_366_ = 3ULL;
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
lean_inc(v_a_253_);
lean_inc(v_fst_289_);
v___x_373_ = l_Lean_Meta_isExprDefEq(v_fst_289_, v_a_253_, v___x_372_, v___y_231_, v___y_232_, v___y_233_);
lean_dec_ref_known(v___x_372_, 7);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; uint8_t v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = lean_unbox(v_a_374_);
lean_dec(v_a_374_);
v_a_294_ = v___x_375_;
goto v___jp_293_;
}
else
{
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_376_; uint8_t v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_373_, 1);
v___x_377_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
v_a_294_ = v___x_377_;
goto v___jp_293_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_del_object(v___x_291_);
lean_dec(v_fst_289_);
lean_del_object(v___x_287_);
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
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
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v_a_391_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_284_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_284_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_280_);
lean_dec(v_a_253_);
v_a_399_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_282_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_282_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v_fst_263_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_fst_263_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_fst_263_, 0);
lean_dec(v_unused_426_);
v___x_410_ = v_fst_263_;
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
else
{
lean_dec(v_fst_263_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = l_Lean_MessageData_ofSyntax(v___x_225_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 7);
lean_ctor_set(v___x_410_, 1, v___x_413_);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_423_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_indentExpr(v_a_253_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 7);
lean_ctor_set(v___x_265_, 1, v___x_416_);
lean_ctor_set(v___x_265_, 0, v___x_415_);
v___x_418_ = v___x_265_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4, &l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once, _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_226_, v___x_420_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_421_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_253_);
lean_dec(v___x_225_);
v_a_429_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_261_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_261_);
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
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_a_250_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec_ref(v___f_223_);
v_a_437_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_252_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_252_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_a_243_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec_ref(v___f_223_);
lean_dec(v___x_222_);
v_a_445_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_249_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_249_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_243_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec_ref(v___f_223_);
lean_dec(v___x_222_);
v_a_453_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_244_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_244_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_241_);
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec_ref(v___f_223_);
lean_dec(v___x_222_);
v_a_461_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_242_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_242_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v___x_225_);
lean_dec(v___x_224_);
lean_dec_ref(v___f_223_);
lean_dec(v___x_222_);
v_a_469_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_240_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_240_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v___f_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_stx_483_, lean_object* v___vars_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v___x_11770__boxed_492_; lean_object* v_res_493_; 
v___x_11770__boxed_492_ = lean_unbox(v___x_478_);
v_res_493_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(v___x_477_, v___x_11770__boxed_492_, v___x_479_, v___f_480_, v___x_481_, v___x_482_, v_stx_483_, v___vars_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v___vars_484_);
lean_dec(v_stx_483_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(lean_object* v_env_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; lean_object* v_messages_498_; lean_object* v_scopes_499_; lean_object* v_usedQuotCtxts_500_; lean_object* v_nextMacroScope_501_; lean_object* v_maxRecDepth_502_; lean_object* v_ngen_503_; lean_object* v_auxDeclNGen_504_; lean_object* v_infoState_505_; lean_object* v_traceState_506_; lean_object* v_snapshotTasks_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v___x_497_ = lean_st_ref_take(v___y_495_);
v_messages_498_ = lean_ctor_get(v___x_497_, 1);
v_scopes_499_ = lean_ctor_get(v___x_497_, 2);
v_usedQuotCtxts_500_ = lean_ctor_get(v___x_497_, 3);
v_nextMacroScope_501_ = lean_ctor_get(v___x_497_, 4);
v_maxRecDepth_502_ = lean_ctor_get(v___x_497_, 5);
v_ngen_503_ = lean_ctor_get(v___x_497_, 6);
v_auxDeclNGen_504_ = lean_ctor_get(v___x_497_, 7);
v_infoState_505_ = lean_ctor_get(v___x_497_, 8);
v_traceState_506_ = lean_ctor_get(v___x_497_, 9);
v_snapshotTasks_507_ = lean_ctor_get(v___x_497_, 10);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_518_);
v___x_509_ = v___x_497_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snapshotTasks_507_);
lean_inc(v_traceState_506_);
lean_inc(v_infoState_505_);
lean_inc(v_auxDeclNGen_504_);
lean_inc(v_ngen_503_);
lean_inc(v_maxRecDepth_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_usedQuotCtxts_500_);
lean_inc(v_scopes_499_);
lean_inc(v_messages_498_);
lean_dec(v___x_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_env_494_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_env_494_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_messages_498_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_scopes_499_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_usedQuotCtxts_500_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v_maxRecDepth_502_);
lean_ctor_set(v_reuseFailAlloc_516_, 6, v_ngen_503_);
lean_ctor_set(v_reuseFailAlloc_516_, 7, v_auxDeclNGen_504_);
lean_ctor_set(v_reuseFailAlloc_516_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_516_, 9, v_traceState_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 10, v_snapshotTasks_507_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_st_ref_set(v___y_495_, v___x_512_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(lean_object* v_env_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_519_, v___y_520_);
lean_dec(v___y_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(lean_object* v_env_523_, lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; lean_object* v_env_529_; lean_object* v_a_531_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_528_ = lean_st_ref_get(v___y_526_);
v_env_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_env_529_);
lean_dec(v___x_528_);
v___x_541_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_523_, v___y_526_);
lean_dec_ref(v___x_541_);
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
v___x_542_ = lean_apply_3(v_x_524_, v___y_525_, v___y_526_, lean_box(0));
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_529_, v___y_526_);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_552_);
v___x_546_ = v___x_544_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_a_543_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_543_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_542_, 1);
v_a_531_ = v_a_553_;
goto v___jp_530_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v___x_532_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_529_, v___y_526_);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_532_, 0);
lean_dec(v_unused_540_);
v___x_534_ = v___x_532_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v___x_532_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 1);
lean_ctor_set(v___x_534_, 0, v_a_531_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_531_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(lean_object* v_env_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_554_, v_x_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic(lean_object* v_stx_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
lean_inc(v_stx_568_);
v___x_573_ = l_Lean_Syntax_isOfKind(v_stx_568_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v_stx_568_);
v___x_574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v_env_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_575_ = lean_st_ref_get(v_a_570_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_575_);
v___f_577_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = l_Lean_Syntax_getArg(v_stx_568_, v___x_578_);
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = l_Lean_Syntax_getArg(v_stx_568_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(5u);
v___x_583_ = l_Lean_Syntax_getArg(v_stx_568_, v___x_582_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_box(v___x_573_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed), 15, 7);
lean_closure_set(v___f_586_, 0, v___x_579_);
lean_closure_set(v___f_586_, 1, v___x_585_);
lean_closure_set(v___f_586_, 2, v___x_581_);
lean_closure_set(v___f_586_, 3, v___f_577_);
lean_closure_set(v___f_586_, 4, v___x_584_);
lean_closure_set(v___f_586_, 5, v___x_583_);
lean_closure_set(v___f_586_, 6, v_stx_568_);
v___x_587_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_587_, 0, lean_box(0));
lean_closure_set(v___x_587_, 1, v___f_586_);
v___x_588_ = l_Lean_Environment_unlockAsync(v_env_576_);
v___x_589_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_588_, v___x_587_, v_a_569_, v_a_570_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(lean_object* v_stx_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(lean_object* v_00_u03b1_595_, lean_object* v_ref_596_, lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_ref_596_, v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(lean_object* v_00_u03b1_606_, lean_object* v_ref_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(v_00_u03b1_606_, v_ref_607_, v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v_ref_607_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(lean_object* v_env_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_617_, v___y_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(lean_object* v_env_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(lean_object* v_00_u03b1_627_, lean_object* v_env_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v_env_628_, v_x_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(lean_object* v_00_u03b1_634_, lean_object* v_env_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(v_00_u03b1_634_, v_env_635_, v_x_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(lean_object* v_00_u03b1_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(v_00_u03b1_651_, v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(lean_object* v_msgData_661_, lean_object* v_macroStack_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_661_, v_macroStack_662_, v___y_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_671_, lean_object* v_macroStack_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_671_, v_macroStack_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1(){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_690_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_691_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_693_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTactic___boxed), 4, 0);
v___x_694_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_690_, v___x_691_, v___x_692_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3(){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3));
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6));
v___x_725_ = l_Lean_addBuiltinDeclarationRanges(v___x_723_, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(lean_object* v_a_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(lean_object* v_00_u03b1_746_, lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(lean_object* v_00_u03b1_756_, lean_object* v_a_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(v_00_u03b1_756_, v_a_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Elab_runTactic(v___x_766_, v___x_767_, v___x_768_, v___x_769_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(v___x_795_, v___x_796_, v___x_797_, v___x_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(lean_object* v_stx_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_x_808_);
return v___x_815_;
}
else
{
lean_object* v_head_816_; lean_object* v_tail_817_; lean_object* v___x_818_; 
v_head_816_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_head_816_);
v_tail_817_ = lean_ctor_get(v_x_809_, 1);
lean_inc(v_tail_817_);
lean_dec_ref_known(v_x_809_, 2);
v___x_818_ = l_Lean_MVarId_getType(v_head_816_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_807_, v_a_819_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_fst_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_831_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v_fst_822_ = lean_ctor_get(v_a_821_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_a_821_, 1);
lean_dec(v_unused_832_);
v___x_824_ = v_a_821_;
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_fst_822_);
lean_dec(v_a_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_indentExpr(v_fst_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 7);
lean_ctor_set(v___x_824_, 1, v___x_826_);
lean_ctor_set(v___x_824_, 0, v_x_808_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_808_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_x_808_ = v___x_828_;
v_x_809_ = v_tail_817_;
goto _start;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_tail_817_);
lean_dec_ref(v_x_808_);
v_a_833_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_820_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_820_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_tail_817_);
lean_dec_ref(v_x_808_);
v_a_841_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_818_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_818_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(lean_object* v_stx_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_849_, v_x_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v_stx_849_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(lean_object* v_stx_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_x_859_);
return v___x_868_;
}
else
{
lean_object* v_head_869_; lean_object* v_tail_870_; lean_object* v___x_871_; 
v_head_869_ = lean_ctor_get(v_x_860_, 0);
lean_inc(v_head_869_);
v_tail_870_ = lean_ctor_get(v_x_860_, 1);
lean_inc(v_tail_870_);
lean_dec_ref_known(v_x_860_, 2);
v___x_871_ = l_Lean_MVarId_getType(v_head_869_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_858_, v_a_872_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v_fst_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v_fst_875_ = lean_ctor_get(v_a_874_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_a_874_, 1);
lean_dec(v_unused_885_);
v___x_877_ = v_a_874_;
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_fst_875_);
lean_dec(v_a_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l_Lean_indentExpr(v_fst_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 7);
lean_ctor_set(v___x_877_, 1, v___x_879_);
lean_ctor_set(v___x_877_, 0, v_x_859_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_x_859_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_858_, v___x_881_, v_tail_870_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v___x_882_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_tail_870_);
lean_dec_ref(v_x_859_);
v_a_886_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_873_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_873_);
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
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_tail_870_);
lean_dec_ref(v_x_859_);
v_a_894_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_871_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_871_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(lean_object* v_stx_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_902_, v_x_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v_stx_902_);
return v_res_912_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(lean_object* v___x_925_, uint8_t v___x_926_, lean_object* v___x_927_, lean_object* v_stx_928_, lean_object* v___f_929_, lean_object* v___x_930_, lean_object* v___vars_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___y_943_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
lean_inc(v___x_925_);
v___x_1040_ = l_Lean_Elab_Term_elabTerm(v___x_925_, v___x_1039_, v___x_926_, v___x_926_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc_n(v_a_1041_, 2);
lean_dec_ref_known(v___x_1040_, 1);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
v___x_1042_ = lean_infer_type(v_a_1041_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(v_a_1041_, v_a_1043_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_a_1045_);
v___x_1047_ = 0;
v___x_1048_ = lean_box(0);
v___x_1049_ = l_Lean_Meta_mkFreshExprMVar(v___x_1046_, v___x_1047_, v___x_1048_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_Expr_mvarId_x21(v_a_1050_);
lean_dec(v_a_1050_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_box(1);
v___x_1054_ = 0;
v___x_1055_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0));
v___x_1056_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1056_, 0, v___x_1039_);
lean_ctor_set(v___x_1056_, 1, v___x_1052_);
lean_ctor_set(v___x_1056_, 2, v___x_1039_);
lean_ctor_set(v___x_1056_, 3, v___f_929_);
lean_ctor_set(v___x_1056_, 4, v___x_1053_);
lean_ctor_set(v___x_1056_, 5, v___x_1053_);
lean_ctor_set(v___x_1056_, 6, v___x_1039_);
lean_ctor_set(v___x_1056_, 7, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8, v___x_926_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 1, v___x_926_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 2, v___x_926_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 3, v___x_926_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 4, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 5, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 6, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 7, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 8, v___x_926_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 9, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*8 + 10, v___x_926_);
v___x_1057_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1057_, 0, v___x_930_);
lean_ctor_set(v___x_1057_, 1, v___x_1053_);
lean_ctor_set(v___x_1057_, 2, v___x_1052_);
lean_ctor_set(v___x_1057_, 3, v___x_1052_);
lean_ctor_set(v___x_1057_, 4, v___x_1052_);
lean_ctor_set(v___x_1057_, 5, v___x_1053_);
lean_ctor_set(v___x_1057_, 6, v___x_1052_);
lean_inc(v___x_927_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed), 11, 4);
lean_closure_set(v___f_1058_, 0, v___x_1051_);
lean_closure_set(v___f_1058_, 1, v___x_927_);
lean_closure_set(v___f_1058_, 2, v___x_1056_);
lean_closure_set(v___f_1058_, 3, v___x_1057_);
v___x_1059_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_1058_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1059_) == 0)
{
v___y_943_ = v___x_1059_;
goto v___jp_942_;
}
else
{
lean_object* v_a_1060_; uint8_t v___y_1062_; uint8_t v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
v___x_1063_ = l_Lean_Exception_isInterrupt(v_a_1060_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; 
v___x_1064_ = l_Lean_Exception_isRuntime(v_a_1060_);
v___y_1062_ = v___x_1064_;
goto v___jp_1061_;
}
else
{
lean_dec(v_a_1060_);
v___y_1062_ = v___x_1063_;
goto v___jp_1061_;
}
v___jp_1061_:
{
if (v___y_1062_ == 0)
{
lean_dec_ref_known(v___x_1059_, 1);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
goto v___jp_939_;
}
else
{
v___y_943_ = v___x_1059_;
goto v___jp_942_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v___x_930_);
lean_dec_ref(v___f_929_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_1065_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1049_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1049_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v___x_930_);
lean_dec_ref(v___f_929_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_1073_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1044_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1044_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1041_);
lean_dec(v___x_930_);
lean_dec_ref(v___f_929_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_1081_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1042_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1042_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v___x_930_);
lean_dec_ref(v___f_929_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_1089_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1040_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1040_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
v___jp_939_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
v___jp_942_:
{
if (lean_obj_tag(v___y_943_) == 0)
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v___y_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___y_943_, 1);
if (lean_obj_tag(v_a_944_) == 0)
{
lean_dec(v___x_927_);
lean_dec(v___x_925_);
goto v___jp_939_;
}
else
{
lean_object* v_val_945_; lean_object* v_fst_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1029_; 
v_val_945_ = lean_ctor_get(v_a_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v_a_944_, 1);
v_fst_946_ = lean_ctor_get(v_val_945_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_val_945_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_val_945_, 1);
lean_dec(v_unused_1030_);
v___x_948_ = v_val_945_;
v_isShared_949_ = v_isSharedCheck_1029_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_fst_946_);
lean_dec(v_val_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1029_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
if (lean_obj_tag(v_fst_946_) == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = l_Lean_MessageData_ofSyntax(v___x_927_);
v___x_951_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 7);
lean_ctor_set(v___x_948_, 1, v___x_951_);
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_959_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_954_ = l_Lean_MessageData_ofSyntax(v___x_925_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_928_, v___x_957_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_958_;
}
}
else
{
lean_object* v_tail_960_; 
v_tail_960_ = lean_ctor_get(v_fst_946_, 1);
if (lean_obj_tag(v_tail_960_) == 0)
{
lean_object* v_head_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1007_; 
v_head_961_ = lean_ctor_get(v_fst_946_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_fst_946_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v_fst_946_, 1);
lean_dec(v_unused_1008_);
v___x_963_ = v_fst_946_;
v_isShared_964_ = v_isSharedCheck_1007_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_head_961_);
lean_dec(v_fst_946_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1007_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_MVarId_getType(v_head_961_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(v_stx_928_, v_a_966_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_fst_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_989_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v_fst_969_ = lean_ctor_get(v_a_968_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_a_968_, 1);
lean_dec(v_unused_990_);
v___x_971_ = v_a_968_;
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_fst_969_);
lean_dec(v_a_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_973_ = l_Lean_indentExpr(v_fst_969_);
v___x_974_ = l_Lean_MessageData_ofSyntax(v___x_927_);
v___x_975_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 7);
lean_ctor_set(v___x_971_, 1, v___x_975_);
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_977_ = v___x_971_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_988_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_MessageData_ofSyntax(v___x_925_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 7);
lean_ctor_set(v___x_963_, 1, v___x_978_);
lean_ctor_set(v___x_963_, 0, v___x_977_);
v___x_980_ = v___x_963_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_978_);
v___x_980_ = v_reuseFailAlloc_987_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 7);
lean_ctor_set(v___x_948_, 1, v___x_981_);
lean_ctor_set(v___x_948_, 0, v___x_980_);
v___x_983_ = v___x_948_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_986_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_973_);
v___x_985_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_928_, v___x_984_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_985_;
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_963_);
lean_del_object(v___x_948_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_991_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_967_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_967_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_del_object(v___x_963_);
lean_del_object(v___x_948_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_999_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_965_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_965_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = l_Lean_MessageData_ofSyntax(v___x_927_);
v___x_1010_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 7);
lean_ctor_set(v___x_948_, 1, v___x_1010_);
lean_ctor_set(v___x_948_, 0, v___x_1009_);
v___x_1012_ = v___x_948_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1013_ = l_Lean_MessageData_ofSyntax(v___x_925_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7, &l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once, _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(v_stx_928_, v___x_1016_, v_fst_946_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_928_, v_a_1018_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_1019_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1017_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1017_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
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
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_a_1031_ = lean_ctor_get(v___y_943_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___y_943_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___y_943_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___y_943_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_stx_1100_, lean_object* v___f_1101_, lean_object* v___x_1102_, lean_object* v___vars_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_7169__boxed_1111_; lean_object* v_res_1112_; 
v___x_7169__boxed_1111_ = lean_unbox(v___x_1098_);
v_res_1112_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(v___x_1097_, v___x_7169__boxed_1111_, v___x_1099_, v_stx_1100_, v___f_1101_, v___x_1102_, v___vars_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___vars_1103_);
lean_dec(v_stx_1100_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure(lean_object* v_stx_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
lean_inc(v_stx_1118_);
v___x_1123_ = l_Lean_Syntax_isOfKind(v_stx_1118_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_stx_1118_);
v___x_1124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v_env_1126_; lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1125_ = lean_st_ref_get(v_a_1120_);
v_env_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1126_);
lean_dec(v___x_1125_);
v___f_1127_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4));
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = l_Lean_Syntax_getArg(v_stx_1118_, v___x_1128_);
v___x_1130_ = lean_unsigned_to_nat(3u);
v___x_1131_ = l_Lean_Syntax_getArg(v_stx_1118_, v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_box(v___x_1123_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed), 14, 6);
lean_closure_set(v___f_1134_, 0, v___x_1129_);
lean_closure_set(v___f_1134_, 1, v___x_1133_);
lean_closure_set(v___f_1134_, 2, v___x_1131_);
lean_closure_set(v___f_1134_, 3, v_stx_1118_);
lean_closure_set(v___f_1134_, 4, v___f_1127_);
lean_closure_set(v___f_1134_, 5, v___x_1132_);
v___x_1135_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___boxed), 5, 2);
lean_closure_set(v___x_1135_, 0, lean_box(0));
lean_closure_set(v___x_1135_, 1, v___f_1134_);
v___x_1136_ = l_Lean_Environment_unlockAsync(v_env_1126_);
v___x_1137_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(v___x_1136_, v___x_1135_, v_a_1119_, v_a_1120_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(lean_object* v_stx_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(lean_object* v_stx_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_1143_, v_x_1144_, v_x_1145_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(lean_object* v_stx_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_1154_, v_x_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_stx_1154_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1(){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1172_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1173_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1175_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed), 4, 0);
v___x_1176_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1172_, v___x_1173_, v___x_1174_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3(){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1));
v___x_1206_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6));
v___x_1207_ = l_Lean_addBuiltinDeclarationRanges(v___x_1205_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12(void){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Array_mkArray0(lean_box(0));
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp(lean_object* v_stx_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
lean_inc(v_stx_1235_);
v___x_1239_ = l_Lean_Syntax_isOfKind(v_stx_1235_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_stx_1235_);
v___x_1240_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1237_);
return v___x_1240_;
}
else
{
lean_object* v_ref_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_ref_1241_ = lean_ctor_get(v_a_1236_, 5);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = l_Lean_Syntax_getArg(v_stx_1235_, v___x_1242_);
v___x_1244_ = lean_unsigned_to_nat(3u);
v___x_1245_ = l_Lean_Syntax_getArg(v_stx_1235_, v___x_1244_);
lean_dec(v_stx_1235_);
v___x_1246_ = 0;
v___x_1247_ = l_Lean_SourceInfo_fromRef(v_ref_1241_, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3));
v___x_1249_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2));
lean_inc_n(v___x_1247_, 7);
v___x_1250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3));
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1247_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1247_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1256_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1247_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1259_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1260_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1247_);
lean_ctor_set(v___x_1261_, 1, v___x_1259_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
lean_inc_ref_n(v___x_1261_, 4);
v___x_1262_ = l_Lean_Syntax_node1(v___x_1247_, v___x_1258_, v___x_1261_);
v___x_1263_ = l_Lean_Syntax_node6(v___x_1247_, v___x_1256_, v___x_1257_, v___x_1262_, v___x_1261_, v___x_1261_, v___x_1261_, v___x_1261_);
v___x_1264_ = l_Lean_Syntax_node6(v___x_1247_, v___x_1248_, v___x_1250_, v___x_1243_, v___x_1252_, v___x_1245_, v___x_1254_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v_a_1237_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(lean_object* v_stx_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Elab_CheckTactic_expandCheckSimp(v_stx_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1(){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1277_ = l_Lean_Elab_macroAttribute;
v___x_1278_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1));
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1280_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimp___boxed), 3, 0);
v___x_1281_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1277_, v___x_1278_, v___x_1279_, v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1));
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6));
v___x_1312_ = l_Lean_addBuiltinDeclarationRanges(v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure(lean_object* v_stx_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
lean_inc(v_stx_1321_);
v___x_1325_ = l_Lean_Syntax_isOfKind(v_stx_1321_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v_stx_1321_);
v___x_1326_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1323_);
return v___x_1326_;
}
else
{
lean_object* v_ref_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_ref_1327_ = lean_ctor_get(v_a_1322_, 5);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = l_Lean_Syntax_getArg(v_stx_1321_, v___x_1328_);
lean_dec(v_stx_1321_);
v___x_1330_ = 0;
v___x_1331_ = l_Lean_SourceInfo_fromRef(v_ref_1327_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1));
v___x_1333_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2));
lean_inc_n(v___x_1331_, 6);
v___x_1334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1331_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4));
v___x_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1331_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6));
v___x_1338_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7));
v___x_1339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1331_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
v___x_1340_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9));
v___x_1341_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11));
v___x_1342_ = lean_obj_once(&l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12, &l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once, _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12);
v___x_1343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1331_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
lean_inc_ref_n(v___x_1343_, 4);
v___x_1344_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1340_, v___x_1343_);
v___x_1345_ = l_Lean_Syntax_node6(v___x_1331_, v___x_1338_, v___x_1339_, v___x_1344_, v___x_1343_, v___x_1343_, v___x_1343_, v___x_1343_);
v___x_1346_ = l_Lean_Syntax_node4(v___x_1331_, v___x_1332_, v___x_1334_, v___x_1329_, v___x_1336_, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_a_1323_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(lean_object* v_stx_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(v_stx_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1(){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1359_ = l_Lean_Elab_macroAttribute;
v___x_1360_ = ((lean_object*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1));
v___x_1361_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1362_ = lean_alloc_closure((void*)(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed), 3, 0);
v___x_1363_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3(){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1));
v___x_1393_ = ((lean_object*)(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6));
v___x_1394_ = l_Lean_addBuiltinDeclarationRanges(v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
return v_res_1396_;
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

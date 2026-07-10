// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVTrace
// Imports: public import Lean.Elab.Tactic.BVDecide.BVCheck import Lean.Meta.Tactic.BVDecide.LRAT.Trim
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
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lrat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "could not find declaration name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "could not find file name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 230, 11, 166, 96, 155, 151, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value),LEAN_SCALAR_PTR_LITERAL(240, 99, 199, 244, 147, 253, 171, 138)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 155, 100, 116, 193, 25, 35, 193)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 158, 162, 202, 28, 96, 104, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_1_){
_start:
{
lean_object* v_ref_3_; uint8_t v___x_4_; lean_object* v___x_5_; 
v_ref_3_ = lean_ctor_get(v___y_1_, 5);
v___x_4_ = 0;
v___x_5_ = l_Lean_Syntax_getPos_x3f(v_ref_3_, v___x_4_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
v_val_8_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_15_ == 0)
{
v___x_10_ = v___x_5_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_val_8_);
lean_dec(v___x_5_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set_tag(v___x_10_, 0);
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_val_8_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_16_);
lean_dec_ref(v___y_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v_env_42_; lean_object* v___x_43_; lean_object* v_mctx_44_; lean_object* v_lctx_45_; lean_object* v_options_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_41_ = lean_st_ref_get(v___y_39_);
v_env_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_env_42_);
lean_dec(v___x_41_);
v___x_43_ = lean_st_ref_get(v___y_37_);
v_mctx_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_mctx_44_);
lean_dec(v___x_43_);
v_lctx_45_ = lean_ctor_get(v___y_36_, 2);
v_options_46_ = lean_ctor_get(v___y_38_, 2);
lean_inc_ref(v_options_46_);
lean_inc_ref(v_lctx_45_);
v___x_47_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_47_, 0, v_env_42_);
lean_ctor_set(v___x_47_, 1, v_mctx_44_);
lean_ctor_set(v___x_47_, 2, v_lctx_45_);
lean_ctor_set(v___x_47_, 3, v_options_46_);
v___x_48_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_msgData_35_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1___boxed(lean_object* v_msgData_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(v_msgData_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(lean_object* v_opts_57_, lean_object* v_opt_58_){
_start:
{
lean_object* v_name_59_; lean_object* v_defValue_60_; lean_object* v_map_61_; lean_object* v___x_62_; 
v_name_59_ = lean_ctor_get(v_opt_58_, 0);
v_defValue_60_ = lean_ctor_get(v_opt_58_, 1);
v_map_61_ = lean_ctor_get(v_opts_57_, 0);
v___x_62_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_61_, v_name_59_);
if (lean_obj_tag(v___x_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = lean_unbox(v_defValue_60_);
return v___x_63_;
}
else
{
lean_object* v_val_64_; 
v_val_64_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_62_, 1);
if (lean_obj_tag(v_val_64_) == 1)
{
uint8_t v_v_65_; 
v_v_65_ = lean_ctor_get_uint8(v_val_64_, 0);
lean_dec_ref_known(v_val_64_, 0);
return v_v_65_;
}
else
{
uint8_t v___x_66_; 
lean_dec(v_val_64_);
v___x_66_ = lean_unbox(v_defValue_60_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_opts_67_, v_opt_68_);
lean_dec_ref(v_opt_68_);
lean_dec_ref(v_opts_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_box(1);
v___x_72_ = l_Lean_MessageData_ofFormat(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2));
v___x_77_ = l_Lean_MessageData_ofFormat(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
return v_x_78_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_103_; 
v_head_80_ = lean_ctor_get(v_x_79_, 0);
v_tail_81_ = lean_ctor_get(v_x_79_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_103_ == 0)
{
v___x_83_ = v_x_79_;
v_isShared_84_ = v_isSharedCheck_103_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_head_80_);
lean_dec(v_x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_103_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_before_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_101_; 
v_before_85_ = lean_ctor_get(v_head_80_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_head_80_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_head_80_, 1);
lean_dec(v_unused_102_);
v___x_87_ = v_head_80_;
v_isShared_88_ = v_isSharedCheck_101_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_before_85_);
lean_dec(v_head_80_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_101_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_89_);
lean_ctor_set(v___x_87_, 0, v_x_78_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_x_78_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_100_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 7);
lean_ctor_set(v___x_83_, 1, v___x_92_);
lean_ctor_set(v___x_83_, 0, v___x_91_);
v___x_94_ = v___x_83_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_92_);
v___x_94_ = v_reuseFailAlloc_99_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Lean_MessageData_ofSyntax(v_before_85_);
v___x_96_ = l_Lean_indentD(v___x_95_);
v___x_97_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_94_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v_x_78_ = v___x_97_;
v_x_79_ = v_tail_81_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1));
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(lean_object* v_msgData_109_, lean_object* v_macroStack_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_options_113_; lean_object* v___x_114_; uint8_t v___x_115_; uint8_t v___x_116_; 
v_options_113_ = lean_ctor_get(v___y_111_, 2);
v___x_114_ = l_Lean_Elab_pp_macroStack;
v___x_115_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_options_113_, v___x_114_);
v___x_116_ = lean_bool_not(v___x_115_);
if (v___x_116_ == 0)
{
if (lean_obj_tag(v_macroStack_110_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_msgData_109_);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_after_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_134_; 
v_head_118_ = lean_ctor_get(v_macroStack_110_, 0);
lean_inc(v_head_118_);
v_after_119_ = lean_ctor_get(v_head_118_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_head_118_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_head_118_, 0);
lean_dec(v_unused_135_);
v___x_121_ = v_head_118_;
v_isShared_122_ = v_isSharedCheck_134_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_after_119_);
lean_dec(v_head_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_134_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 7);
lean_ctor_set(v___x_121_, 1, v___x_123_);
lean_ctor_set(v___x_121_, 0, v_msgData_109_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_msgData_109_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_133_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_msgData_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_126_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2);
v___x_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = l_Lean_MessageData_ofSyntax(v_after_119_);
v___x_129_ = l_Lean_indentD(v___x_128_);
v_msgData_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_130_, 0, v___x_127_);
lean_ctor_set(v_msgData_130_, 1, v___x_129_);
v___x_131_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4(v_msgData_130_, v_macroStack_110_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_macroStack_110_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v_msgData_109_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_137_, lean_object* v_macroStack_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_137_, v_macroStack_138_, v___y_139_);
lean_dec_ref(v___y_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(lean_object* v_msg_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_ref_150_; lean_object* v___x_151_; lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_ref_150_ = lean_ctor_get(v___y_147_, 5);
v___x_151_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(v_msg_142_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_151_);
v_macroStack_153_ = lean_ctor_get(v___y_143_, 1);
v___x_154_ = l_Lean_Elab_getBetterRef(v_ref_150_, v_macroStack_153_);
lean_inc(v_macroStack_153_);
v___x_155_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_a_152_, v_macroStack_153_, v___y_147_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_154_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg___boxed(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2));
v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4));
v___x_181_ = l_Lean_stringToMessageData(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_fileName_189_; lean_object* v_fileMap_190_; lean_object* v___x_191_; 
v_fileName_189_ = lean_ctor_get(v_a_186_, 0);
v_fileMap_190_ = lean_ctor_get(v_a_186_, 1);
lean_inc_ref(v_fileName_189_);
v___x_191_ = l_System_FilePath_fileName(v_fileName_189_);
if (lean_obj_tag(v___x_191_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_193_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_182_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
if (lean_obj_tag(v_a_194_) == 1)
{
lean_object* v_val_195_; lean_object* v___x_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_220_; 
v_val_195_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v_a_194_, 1);
v___x_196_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_186_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_220_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v_line_202_; lean_object* v_column_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_inc_ref(v_fileMap_190_);
v___x_201_ = l_Lean_FileMap_toPosition(v_fileMap_190_, v_a_197_);
lean_dec(v_a_197_);
v_line_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_line_202_);
v_column_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_column_203_);
lean_dec_ref(v___x_201_);
v___x_204_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0));
v___x_205_ = lean_string_append(v_val_192_, v___x_204_);
v___x_206_ = 1;
v___x_207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_195_, v___x_206_);
v___x_208_ = lean_string_append(v___x_205_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_string_append(v___x_208_, v___x_204_);
v___x_210_ = l_Nat_reprFast(v_line_202_);
v___x_211_ = lean_string_append(v___x_209_, v___x_210_);
lean_dec_ref(v___x_210_);
v___x_212_ = lean_string_append(v___x_211_, v___x_204_);
v___x_213_ = l_Nat_reprFast(v_column_203_);
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1));
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_216_);
v___x_218_ = v___x_199_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_a_194_);
lean_dec(v_val_192_);
v___x_221_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
v___x_222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v___x_221_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_222_;
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_val_192_);
v_a_223_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_193_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_193_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v___x_191_);
v___x_231_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5);
v___x_232_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v___x_231_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1(lean_object* v_00_u03b1_241_, lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___boxed(lean_object* v_00_u03b1_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1(v_00_u03b1_251_, v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2(lean_object* v_msgData_261_, lean_object* v_macroStack_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_261_, v_macroStack_262_, v___y_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___boxed(lean_object* v_msgData_271_, lean_object* v_macroStack_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2(v_msgData_271_, v_macroStack_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_box(0);
v___x_282_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
v___x_321_ = lean_apply_9(v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, lean_box(0));
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___f_344_; lean_object* v___x_345_; 
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_344_, 0, v_x_334_);
lean_closure_set(v___f_344_, 1, v___y_335_);
lean_closure_set(v___f_344_, 2, v___y_336_);
lean_closure_set(v___f_344_, 3, v___y_337_);
lean_closure_set(v___f_344_, 4, v___y_338_);
v___x_345_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_333_, v___f_344_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_345_) == 0)
{
return v___x_345_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_354_, v_x_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_366_, lean_object* v_mvarId_367_, lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_367_, v_x_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_379_, lean_object* v_mvarId_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(v_00_u03b1_379_, v_mvarId_380_, v_x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_392_){
_start:
{
if (lean_obj_tag(v_e_392_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v_e_392_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_e_392_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_e_392_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v_e_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_mk_io_user_error(v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 1);
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_403_ = lean_ctor_get(v_e_392_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_e_392_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v_e_392_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v_e_392_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_414_, lean_object* v_e_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v_e_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_418_, lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(v_00_u03b1_418_, v_e_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0(lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(v_a_422_, v_a_423_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0___boxed(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0(v_a_434_, v_a_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Array_mkArray0(lean_box(0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(lean_object* v_x_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4));
lean_inc(v_x_483_);
v___x_494_ = l_Lean_Syntax_isOfKind(v_x_483_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_x_483_);
v___x_495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = l_Lean_Syntax_getArg(v_x_483_, v___x_496_);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6));
lean_inc(v___x_497_);
v___x_499_ = l_Lean_Syntax_isOfKind(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v___x_500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_500_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_501_ = lean_unsigned_to_nat(10u);
v___x_502_ = 0;
v___x_503_ = lean_unsigned_to_nat(100000u);
v___x_504_ = 0;
v___x_505_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_505_, 0, v___x_501_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 1, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 2, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 3, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 4, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 5, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 6, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 7, v___x_499_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 8, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 9, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 10, v___x_504_);
lean_inc(v___x_497_);
v___x_506_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v___x_497_, v___x_505_, v___x_499_, v_a_484_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_timeout_510_; uint8_t v_binaryProofs_511_; uint8_t v_acNf_512_; uint8_t v_andFlattening_513_; uint8_t v_embeddedConstraintSubst_514_; uint8_t v_structures_515_; uint8_t v_fixedInt_516_; uint8_t v_enums_517_; uint8_t v_graphviz_518_; lean_object* v_maxSteps_519_; uint8_t v_shortCircuit_520_; uint8_t v_solverMode_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_669_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v_timeout_510_ = lean_ctor_get(v_a_507_, 0);
v_binaryProofs_511_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 1);
v_acNf_512_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 2);
v_andFlattening_513_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_514_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 4);
v_structures_515_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 5);
v_fixedInt_516_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 6);
v_enums_517_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 7);
v_graphviz_518_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 8);
v_maxSteps_519_ = lean_ctor_get(v_a_507_, 1);
v_shortCircuit_520_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 9);
v_solverMode_521_ = lean_ctor_get_uint8(v_a_507_, sizeof(void*)*2 + 10);
v_isSharedCheck_669_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_669_ == 0)
{
v___x_523_ = v_a_507_;
v_isShared_524_ = v_isSharedCheck_669_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_maxSteps_519_);
lean_inc(v_timeout_510_);
lean_dec(v_a_507_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_669_;
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
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_timeout_510_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_maxSteps_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 1, v_binaryProofs_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 2, v_acNf_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 3, v_andFlattening_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 5, v_structures_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 6, v_fixedInt_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 7, v_enums_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 8, v_graphviz_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 9, v_shortCircuit_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*2 + 10, v_solverMode_521_);
v___x_526_ = v_reuseFailAlloc_668_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*2, v___x_502_);
lean_inc(v_a_509_);
v___x_527_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v_a_509_, v___x_526_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_485_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_n(v_a_530_, 2);
lean_dec_ref_known(v___x_529_, 1);
lean_inc(v_a_528_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0___boxed), 11, 2);
lean_closure_set(v___f_531_, 0, v_a_530_);
lean_closure_set(v___f_531_, 1, v_a_528_);
v___x_532_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_a_530_, v___f_531_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v_tk_535_; lean_object* v___y_537_; lean_object* v___y_538_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = lean_unsigned_to_nat(0u);
v_tk_535_ = l_Lean_Syntax_getArg(v_x_483_, v___x_534_);
lean_dec(v_x_483_);
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v_ref_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_a_528_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
v_ref_556_ = lean_ctor_get(v_a_490_, 5);
v___x_557_ = l_Lean_SourceInfo_fromRef(v_ref_556_, v___x_502_);
v___x_558_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8));
v___x_559_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14));
v___x_560_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15));
lean_inc_n(v___x_557_, 3);
v___x_561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17));
v___x_563_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18, &l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18);
v___x_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_557_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
v___x_565_ = l_Lean_Syntax_node1(v___x_557_, v___x_498_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node2(v___x_557_, v___x_559_, v___x_561_, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_558_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v_a_533_);
lean_ctor_set(v___x_569_, 2, v_a_533_);
lean_ctor_set(v___x_569_, 3, v___x_568_);
lean_ctor_set(v___x_569_, 4, v___x_568_);
lean_ctor_set(v___x_569_, 5, v___x_568_);
lean_inc(v_ref_556_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v_ref_556_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12));
v___x_572_ = 4;
v___x_573_ = l_Lean_MessageData_nil;
v___x_574_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_535_, v___x_569_, v___x_570_, v___x_571_, v_a_533_, v___x_572_, v___x_573_, v_a_490_, v_a_491_);
return v___x_574_;
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_642_; 
v_isSharedCheck_642_ = !lean_is_exclusive(v_a_533_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v_a_533_, 0);
lean_dec(v_unused_643_);
v___x_576_ = v_a_533_;
v_isShared_577_ = v_isSharedCheck_642_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_a_533_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_642_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_config_578_; uint8_t v_trimProofs_579_; 
v_config_578_ = lean_ctor_get(v_a_528_, 5);
lean_inc_ref(v_config_578_);
lean_dec(v_a_528_);
v_trimProofs_579_ = lean_ctor_get_uint8(v_config_578_, sizeof(void*)*2);
lean_dec_ref(v_config_578_);
if (v_trimProofs_579_ == 0)
{
lean_del_object(v___x_576_);
v___y_537_ = v_a_490_;
v___y_538_ = v_a_491_;
goto v___jp_536_;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
lean_inc(v_a_509_);
v___x_582_ = l_System_FilePath_join(v_a_581_, v_a_509_);
v___x_583_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_584_);
lean_dec(v_a_584_);
v___x_586_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v___x_582_, v_a_587_, v_binaryProofs_511_);
lean_dec(v_a_587_);
lean_dec_ref(v___x_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref_known(v___x_588_, 1);
lean_del_object(v___x_576_);
v___y_537_ = v_a_490_;
v___y_538_ = v_a_491_;
goto v___jp_536_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_tk_535_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_603_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_ref_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v_ref_593_ = lean_ctor_get(v_a_490_, 5);
v___x_594_ = lean_io_error_to_string(v_a_589_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 3);
lean_ctor_set(v___x_576_, 0, v___x_594_);
v___x_596_ = v___x_576_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_602_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = l_Lean_MessageData_ofFormat(v___x_596_);
lean_inc(v_ref_593_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_ref_593_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_600_ = v___x_591_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v___x_582_);
lean_dec(v_tk_535_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
v_a_604_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_618_ == 0)
{
v___x_606_ = v___x_586_;
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_586_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_618_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_ref_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v_ref_608_ = lean_ctor_get(v_a_490_, 5);
v___x_609_ = lean_io_error_to_string(v_a_604_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 3);
lean_ctor_set(v___x_576_, 0, v___x_609_);
v___x_611_ = v___x_576_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_612_ = l_Lean_MessageData_ofFormat(v___x_611_);
lean_inc(v_ref_608_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_ref_608_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_613_);
v___x_615_ = v___x_606_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v___x_582_);
lean_dec(v_tk_535_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
v_a_619_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v___x_583_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_583_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_ref_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_ref_623_ = lean_ctor_get(v_a_490_, 5);
v___x_624_ = lean_io_error_to_string(v_a_619_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 3);
lean_ctor_set(v___x_576_, 0, v___x_624_);
v___x_626_ = v___x_576_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_632_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = l_Lean_MessageData_ofFormat(v___x_626_);
lean_inc(v_ref_623_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_ref_623_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_628_);
v___x_630_ = v___x_621_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_del_object(v___x_576_);
lean_dec(v_tk_535_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
v_a_634_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_580_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_580_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
v___jp_536_:
{
lean_object* v_ref_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_ref_539_ = lean_ctor_get(v___y_537_, 5);
v___x_540_ = l_Lean_SourceInfo_fromRef(v_ref_539_, v___x_502_);
v___x_541_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8));
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10));
v___x_543_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11));
lean_inc(v___x_540_);
v___x_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_540_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_box(2);
v___x_546_ = l_Lean_Syntax_mkStrLit(v_a_509_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node3(v___x_540_, v___x_542_, v___x_544_, v___x_497_, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_541_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
lean_ctor_set(v___x_550_, 4, v___x_549_);
lean_ctor_set(v___x_550_, 5, v___x_549_);
lean_inc(v_ref_539_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_ref_539_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12));
v___x_553_ = 4;
v___x_554_ = l_Lean_MessageData_nil;
v___x_555_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_535_, v___x_550_, v___x_551_, v___x_552_, v___x_549_, v___x_553_, v___x_554_, v___y_537_, v___y_538_);
return v___x_555_;
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_a_528_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v_a_644_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_532_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_532_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_528_);
lean_dec(v_a_509_);
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v_a_652_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_529_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_529_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_a_509_);
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v_a_660_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_527_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_527_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_507_);
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v_a_670_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_508_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_508_);
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
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v___x_497_);
lean_dec(v_x_483_);
v_a_678_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_506_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_506_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object* v_x_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(v_x_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1(){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_709_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4));
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4));
v___x_712_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 10, 0);
v___x_713_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_709_, v___x_710_, v___x_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___boxed(lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1();
return v_res_715_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_BVCheck(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
}
#ifdef __cplusplus
}
#endif

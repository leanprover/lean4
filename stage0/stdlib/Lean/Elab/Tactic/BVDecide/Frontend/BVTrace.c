// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
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
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lrat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "could not find declaration name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "could not find file name"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 230, 11, 166, 96, 155, 151, 146)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13_value),LEAN_SCALAR_PTR_LITERAL(240, 99, 199, 244, 147, 253, 171, 138)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 103, 168, 183, 71, 3, 149, 84)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 53, 205, 211, 1, 94, 148, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(lean_object* v___y_1_){
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
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(v___y_16_);
lean_dec_ref(v___y_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(v___y_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___boxed(lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_34_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(1);
v___x_36_ = l_Lean_MessageData_ofFormat(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2));
v___x_41_ = l_Lean_MessageData_ofFormat(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
return v_x_42_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_67_; 
v_head_44_ = lean_ctor_get(v_x_43_, 0);
v_tail_45_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_67_ == 0)
{
v___x_47_ = v_x_43_;
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_head_44_);
lean_dec(v_x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_before_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_65_; 
v_before_49_ = lean_ctor_get(v_head_44_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v_head_44_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v_head_44_, 1);
lean_dec(v_unused_66_);
v___x_51_ = v_head_44_;
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_before_49_);
lean_dec(v_head_44_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 7);
lean_ctor_set(v___x_51_, 1, v___x_53_);
lean_ctor_set(v___x_51_, 0, v_x_42_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_x_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_64_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 7);
lean_ctor_set(v___x_47_, 1, v___x_56_);
lean_ctor_set(v___x_47_, 0, v___x_55_);
v___x_58_ = v___x_47_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_63_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = l_Lean_MessageData_ofSyntax(v_before_49_);
v___x_60_ = l_Lean_indentD(v___x_59_);
v___x_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_58_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v_x_42_ = v___x_61_;
v_x_43_ = v_tail_45_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3(lean_object* v_opts_68_, lean_object* v_opt_69_){
_start:
{
lean_object* v_name_70_; lean_object* v_defValue_71_; lean_object* v_map_72_; lean_object* v___x_73_; 
v_name_70_ = lean_ctor_get(v_opt_69_, 0);
v_defValue_71_ = lean_ctor_get(v_opt_69_, 1);
v_map_72_ = lean_ctor_get(v_opts_68_, 0);
v___x_73_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_72_, v_name_70_);
if (lean_obj_tag(v___x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = lean_unbox(v_defValue_71_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; 
v_val_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v___x_73_);
if (lean_obj_tag(v_val_75_) == 1)
{
uint8_t v_v_76_; 
v_v_76_ = lean_ctor_get_uint8(v_val_75_, 0);
lean_dec_ref(v_val_75_);
return v_v_76_;
}
else
{
uint8_t v___x_77_; 
lean_dec(v_val_75_);
v___x_77_ = lean_unbox(v_defValue_71_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_78_, lean_object* v_opt_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_opts_78_, v_opt_79_);
lean_dec_ref(v_opt_79_);
lean_dec_ref(v_opts_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1));
v___x_86_ = l_Lean_MessageData_ofFormat(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg(lean_object* v_msgData_87_, lean_object* v_macroStack_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_options_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_options_91_ = lean_ctor_get(v___y_89_, 2);
v___x_92_ = l_Lean_Elab_pp_macroStack;
v___x_93_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_options_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_macroStack_88_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_msgData_87_);
return v___x_94_;
}
else
{
if (lean_obj_tag(v_macroStack_88_) == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v_msgData_87_);
return v___x_95_;
}
else
{
lean_object* v_head_96_; lean_object* v_after_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_112_; 
v_head_96_ = lean_ctor_get(v_macroStack_88_, 0);
lean_inc(v_head_96_);
v_after_97_ = lean_ctor_get(v_head_96_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_head_96_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v_head_96_, 0);
lean_dec(v_unused_113_);
v___x_99_ = v_head_96_;
v_isShared_100_ = v_isSharedCheck_112_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_after_97_);
lean_dec(v_head_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_112_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 7);
lean_ctor_set(v___x_99_, 1, v___x_101_);
lean_ctor_set(v___x_99_, 0, v_msgData_87_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_msgData_87_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_111_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_msgData_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_104_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2);
v___x_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = l_Lean_MessageData_ofSyntax(v_after_97_);
v___x_107_ = l_Lean_indentD(v___x_106_);
v_msgData_108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_108_, 0, v___x_105_);
lean_ctor_set(v_msgData_108_, 1, v___x_107_);
v___x_109_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2_spec__4(v_msgData_108_, v_macroStack_88_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_114_, lean_object* v_macroStack_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_114_, v_macroStack_115_, v___y_116_);
lean_dec_ref(v___y_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; lean_object* v_env_126_; lean_object* v___x_127_; lean_object* v_mctx_128_; lean_object* v_lctx_129_; lean_object* v_options_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_125_ = lean_st_ref_get(v___y_123_);
v_env_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc_ref(v_env_126_);
lean_dec(v___x_125_);
v___x_127_ = lean_st_ref_get(v___y_121_);
v_mctx_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref(v_mctx_128_);
lean_dec(v___x_127_);
v_lctx_129_ = lean_ctor_get(v___y_120_, 2);
v_options_130_ = lean_ctor_get(v___y_122_, 2);
lean_inc_ref(v_options_130_);
lean_inc_ref(v_lctx_129_);
v___x_131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_131_, 0, v_env_126_);
lean_ctor_set(v___x_131_, 1, v_mctx_128_);
lean_ctor_set(v___x_131_, 2, v_lctx_129_);
lean_ctor_set(v___x_131_, 3, v_options_130_);
v___x_132_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_msgData_119_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1___boxed(lean_object* v_msgData_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1(v_msgData_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(lean_object* v_msg_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_ref_149_; lean_object* v___x_150_; lean_object* v_a_151_; lean_object* v_macroStack_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_163_; 
v_ref_149_ = lean_ctor_get(v___y_146_, 5);
v___x_150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__1(v_msg_141_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v___x_150_);
v_macroStack_152_ = lean_ctor_get(v___y_142_, 1);
lean_inc_n(v_macroStack_152_, 2);
v___x_153_ = l_Lean_Elab_getBetterRef(v_ref_149_, v_macroStack_152_);
v___x_154_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_a_151_, v_macroStack_152_, v___y_146_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_163_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_153_);
lean_ctor_set(v___x_159_, 1, v_a_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 1);
lean_ctor_set(v___x_157_, 0, v___x_159_);
v___x_161_ = v___x_157_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg___boxed(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_172_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2));
v___x_177_ = l_Lean_stringToMessageData(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_fileName_188_; lean_object* v_fileMap_189_; lean_object* v___x_190_; 
v_fileName_188_ = lean_ctor_get(v_a_185_, 0);
v_fileMap_189_ = lean_ctor_get(v_a_185_, 1);
lean_inc_ref(v_fileName_188_);
v___x_190_ = l_System_FilePath_fileName(v_fileName_188_);
if (lean_obj_tag(v___x_190_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; 
v_val_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v___x_190_);
v___x_192_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_181_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref(v___x_192_);
if (lean_obj_tag(v_a_193_) == 1)
{
lean_object* v_val_194_; lean_object* v___x_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_219_; 
v_val_194_ = lean_ctor_get(v_a_193_, 0);
lean_inc(v_val_194_);
lean_dec_ref(v_a_193_);
v___x_195_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(v_a_185_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_219_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_219_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_219_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v_line_201_; lean_object* v_column_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc_ref(v_fileMap_189_);
v___x_200_ = l_Lean_FileMap_toPosition(v_fileMap_189_, v_a_196_);
lean_dec(v_a_196_);
v_line_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_line_201_);
v_column_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_column_202_);
lean_dec_ref(v___x_200_);
v___x_203_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0));
v___x_204_ = lean_string_append(v_val_191_, v___x_203_);
v___x_205_ = 1;
v___x_206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_194_, v___x_205_);
v___x_207_ = lean_string_append(v___x_204_, v___x_206_);
lean_dec_ref(v___x_206_);
v___x_208_ = lean_string_append(v___x_207_, v___x_203_);
v___x_209_ = l_Nat_reprFast(v_line_201_);
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_string_append(v___x_210_, v___x_203_);
v___x_212_ = l_Nat_reprFast(v_column_202_);
v___x_213_ = lean_string_append(v___x_211_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1));
v___x_215_ = lean_string_append(v___x_213_, v___x_214_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_215_);
v___x_217_ = v___x_198_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_a_193_);
lean_dec(v_val_191_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3);
v___x_221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(v___x_220_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v___x_221_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_val_191_);
v_a_222_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_192_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_192_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v___x_190_);
v___x_230_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5);
v___x_231_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(v___x_230_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1(lean_object* v_00_u03b1_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___redArg(v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1___boxed(lean_object* v_00_u03b1_250_, lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1(v_00_u03b1_250_, v_msg_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2(lean_object* v_msgData_260_, lean_object* v_macroStack_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_260_, v_macroStack_261_, v___y_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2___boxed(lean_object* v_msgData_270_, lean_object* v_macroStack_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__1_spec__2(v_msgData_270_, v_macroStack_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_279_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_box(0);
v___x_281_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___boxed(lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg();
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(lean_object* v_00_u03b1_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___boxed(lean_object* v_00_u03b1_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(v_00_u03b1_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
v___x_320_ = lean_apply_9(v_x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, lean_box(0));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_332_, lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___f_343_; lean_object* v___x_344_; 
lean_inc(v___y_337_);
lean_inc_ref(v___y_336_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_343_, 0, v_x_333_);
lean_closure_set(v___f_343_, 1, v___y_334_);
lean_closure_set(v___f_343_, 2, v___y_335_);
lean_closure_set(v___f_343_, 3, v___y_336_);
lean_closure_set(v___f_343_, 4, v___y_337_);
v___x_344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_332_, v___f_343_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_344_) == 0)
{
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_353_, lean_object* v_x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_353_, v_x_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1(lean_object* v_00_u03b1_365_, lean_object* v_mvarId_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_378_, lean_object* v_mvarId_379_, lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1(v_00_u03b1_378_, v_mvarId_379_, v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(lean_object* v_e_391_){
_start:
{
if (lean_obj_tag(v_e_391_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_e_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_e_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_e_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_e_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_mk_io_user_error(v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v_e_391_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_e_391_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v_e_391_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v_e_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg___boxed(lean_object* v_e_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(v_e_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2(lean_object* v_00_u03b1_413_, lean_object* v_e_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(v_e_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___boxed(lean_object* v_00_u03b1_417_, lean_object* v_e_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2(v_00_u03b1_417_, v_e_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(v_a_421_, v_a_422_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(v_a_433_, v_a_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18(void){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Array_mkArray0(lean_box(0));
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object* v_x_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4));
lean_inc(v_x_482_);
v___x_493_ = l_Lean_Syntax_isOfKind(v_x_482_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_x_482_);
v___x_494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = l_Lean_Syntax_getArg(v_x_482_, v___x_495_);
v___x_497_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6));
lean_inc(v___x_496_);
v___x_498_ = l_Lean_Syntax_isOfKind(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v___x_499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg();
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_inc(v___x_496_);
v___x_500_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v___x_496_, v_a_483_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_timeout_504_; uint8_t v_binaryProofs_505_; uint8_t v_acNf_506_; uint8_t v_andFlattening_507_; uint8_t v_embeddedConstraintSubst_508_; uint8_t v_structures_509_; uint8_t v_fixedInt_510_; uint8_t v_enums_511_; uint8_t v_graphviz_512_; lean_object* v_maxSteps_513_; uint8_t v_shortCircuit_514_; uint8_t v_solverMode_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_662_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v_timeout_504_ = lean_ctor_get(v_a_501_, 0);
v_binaryProofs_505_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 1);
v_acNf_506_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 2);
v_andFlattening_507_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_508_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 4);
v_structures_509_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 5);
v_fixedInt_510_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 6);
v_enums_511_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 7);
v_graphviz_512_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 8);
v_maxSteps_513_ = lean_ctor_get(v_a_501_, 1);
v_shortCircuit_514_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 9);
v_solverMode_515_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*2 + 10);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_662_ == 0)
{
v___x_517_ = v_a_501_;
v_isShared_518_ = v_isSharedCheck_662_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_maxSteps_513_);
lean_inc(v_timeout_504_);
lean_dec(v_a_501_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_662_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___x_519_; lean_object* v___x_521_; 
v___x_519_ = 0;
if (v_isShared_518_ == 0)
{
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_timeout_504_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_maxSteps_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 1, v_binaryProofs_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 2, v_acNf_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 3, v_andFlattening_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 5, v_structures_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 6, v_fixedInt_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 7, v_enums_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 8, v_graphviz_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 9, v_shortCircuit_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2 + 10, v_solverMode_515_);
v___x_521_ = v_reuseFailAlloc_661_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*2, v___x_519_);
lean_inc(v_a_503_);
v___x_522_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v_a_503_, v___x_521_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_484_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_n(v_a_525_, 2);
lean_dec_ref(v___x_524_);
lean_inc(v_a_523_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed), 11, 2);
lean_closure_set(v___f_526_, 0, v_a_525_);
lean_closure_set(v___f_526_, 1, v_a_523_);
v___x_527_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(v_a_525_, v___f_526_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v_tk_530_; lean_object* v___y_532_; lean_object* v___y_533_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_tk_530_ = l_Lean_Syntax_getArg(v_x_482_, v___x_529_);
lean_dec(v_x_482_);
if (lean_obj_tag(v_a_528_) == 0)
{
lean_object* v_ref_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
lean_dec(v_a_523_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
v_ref_550_ = lean_ctor_get(v_a_489_, 5);
v___x_551_ = l_Lean_SourceInfo_fromRef(v_ref_550_, v___x_519_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8));
v___x_553_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14));
v___x_554_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15));
lean_inc_n(v___x_551_, 3);
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17));
v___x_557_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v___x_551_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
lean_ctor_set(v___x_558_, 2, v___x_557_);
v___x_559_ = l_Lean_Syntax_node1(v___x_551_, v___x_497_, v___x_558_);
v___x_560_ = l_Lean_Syntax_node2(v___x_551_, v___x_553_, v___x_555_, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_552_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v_a_528_);
lean_ctor_set(v___x_563_, 2, v_a_528_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
lean_ctor_set(v___x_563_, 4, v___x_562_);
lean_ctor_set(v___x_563_, 5, v___x_562_);
lean_inc(v_ref_550_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_ref_550_);
v___x_565_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12));
v___x_566_ = 4;
v___x_567_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_530_, v___x_563_, v___x_564_, v___x_565_, v_a_528_, v___x_566_, v_a_489_, v_a_490_);
return v___x_567_;
}
else
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_635_; 
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_528_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_a_528_, 0);
lean_dec(v_unused_636_);
v___x_569_ = v_a_528_;
v_isShared_570_ = v_isSharedCheck_635_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_a_528_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_635_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_config_571_; uint8_t v_trimProofs_572_; 
v_config_571_ = lean_ctor_get(v_a_523_, 5);
lean_inc_ref(v_config_571_);
lean_dec(v_a_523_);
v_trimProofs_572_ = lean_ctor_get_uint8(v_config_571_, sizeof(void*)*2);
lean_dec_ref(v_config_571_);
if (v_trimProofs_572_ == 0)
{
lean_del_object(v___x_569_);
v___y_532_ = v_a_489_;
v___y_533_ = v_a_490_;
goto v___jp_531_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
lean_inc(v_a_503_);
v___x_575_ = l_System_FilePath_join(v_a_574_, v_a_503_);
v___x_576_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v___x_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_a_577_);
lean_dec(v_a_577_);
v___x_579_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(v___x_578_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v___x_575_, v_a_580_, v_binaryProofs_505_);
lean_dec(v_a_580_);
lean_dec_ref(v___x_575_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_dec_ref(v___x_581_);
lean_del_object(v___x_569_);
v___y_532_ = v_a_489_;
v___y_533_ = v_a_490_;
goto v___jp_531_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_tk_530_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_596_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_ref_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_ref_586_ = lean_ctor_get(v_a_489_, 5);
v___x_587_ = lean_io_error_to_string(v_a_582_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 3);
lean_ctor_set(v___x_569_, 0, v___x_587_);
v___x_589_ = v___x_569_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = l_Lean_MessageData_ofFormat(v___x_589_);
lean_inc(v_ref_586_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_ref_586_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_591_);
v___x_593_ = v___x_584_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v___x_575_);
lean_dec(v_tk_530_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
v_a_597_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_611_ == 0)
{
v___x_599_ = v___x_579_;
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_579_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v_ref_601_ = lean_ctor_get(v_a_489_, 5);
v___x_602_ = lean_io_error_to_string(v_a_597_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 3);
lean_ctor_set(v___x_569_, 0, v___x_602_);
v___x_604_ = v___x_569_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_610_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_605_ = l_Lean_MessageData_ofFormat(v___x_604_);
lean_inc(v_ref_601_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_ref_601_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_606_);
v___x_608_ = v___x_599_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v___x_575_);
lean_dec(v_tk_530_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
v_a_612_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_626_ == 0)
{
v___x_614_ = v___x_576_;
v_isShared_615_ = v_isSharedCheck_626_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_576_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_626_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_ref_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v_ref_616_ = lean_ctor_get(v_a_489_, 5);
v___x_617_ = lean_io_error_to_string(v_a_612_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 3);
lean_ctor_set(v___x_569_, 0, v___x_617_);
v___x_619_ = v___x_569_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_625_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = l_Lean_MessageData_ofFormat(v___x_619_);
lean_inc(v_ref_616_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_ref_616_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_621_);
v___x_623_ = v___x_614_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_del_object(v___x_569_);
lean_dec(v_tk_530_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
v_a_627_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_573_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_573_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
v___jp_531_:
{
lean_object* v_ref_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; 
v_ref_534_ = lean_ctor_get(v___y_532_, 5);
v___x_535_ = l_Lean_SourceInfo_fromRef(v_ref_534_, v___x_519_);
v___x_536_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8));
v___x_537_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10));
v___x_538_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11));
lean_inc(v___x_535_);
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_535_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_box(2);
v___x_541_ = l_Lean_Syntax_mkStrLit(v_a_503_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node3(v___x_535_, v___x_537_, v___x_539_, v___x_496_, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_536_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
lean_ctor_set(v___x_545_, 2, v___x_544_);
lean_ctor_set(v___x_545_, 3, v___x_544_);
lean_ctor_set(v___x_545_, 4, v___x_544_);
lean_ctor_set(v___x_545_, 5, v___x_544_);
lean_inc(v_ref_534_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_ref_534_);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12));
v___x_548_ = 4;
v___x_549_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_530_, v___x_545_, v___x_546_, v___x_547_, v___x_544_, v___x_548_, v___y_532_, v___y_533_);
return v___x_549_;
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_523_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v_a_637_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_527_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_527_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_a_523_);
lean_dec(v_a_503_);
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v_a_645_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_524_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_524_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_503_);
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v_a_653_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_522_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_522_);
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
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_a_501_);
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v_a_663_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_502_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_502_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v___x_496_);
lean_dec(v_x_482_);
v_a_671_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_500_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_500_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___boxed(lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(v_x_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_705_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4));
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5));
v___x_707_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___boxed), 10, 0);
v___x_708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_704_, v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1();
return v_res_710_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(builtin);
}
#ifdef __cplusplus
}
#endif

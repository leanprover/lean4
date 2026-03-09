// Lean compiler output
// Module: Lake.CLI.Error
// Imports: public import Init.Data.ToString public import Init.System.FilePath
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
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCliError_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedCliError;
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value;
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lake_instReprCliError_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lake.CliError.unknownLakeInstall"};
static const lean_object* l_Lake_instReprCliError_repr___closed__0 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__1 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__1_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lake.CliError.unknownLeanInstall"};
static const lean_object* l_Lake_instReprCliError_repr___closed__2 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__3 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__3_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lake.CliError.missingCommand"};
static const lean_object* l_Lake_instReprCliError_repr___closed__4 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__5 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__5_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lake.CliError.unexpectedPlus"};
static const lean_object* l_Lake_instReprCliError_repr___closed__6 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__7 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__7_value;
static lean_once_cell_t l_Lake_instReprCliError_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprCliError_repr___closed__8;
static lean_once_cell_t l_Lake_instReprCliError_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprCliError_repr___closed__9;
static const lean_string_object l_Lake_instReprCliError_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lake.CliError.unknownCommand"};
static const lean_object* l_Lake_instReprCliError_repr___closed__10 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__10_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__10_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__11 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__11_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__12 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__12_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lake.CliError.missingArg"};
static const lean_object* l_Lake_instReprCliError_repr___closed__13 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__13_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__13_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__14 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__14_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__15 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__15_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.missingOptArg"};
static const lean_object* l_Lake_instReprCliError_repr___closed__16 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__16_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__16_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__17 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__17_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__18 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__18_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.invalidOptArg"};
static const lean_object* l_Lake_instReprCliError_repr___closed__19 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__19_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__19_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__20 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__20_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__21 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__21_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lake.CliError.unknownShortOption"};
static const lean_object* l_Lake_instReprCliError_repr___closed__22 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__22_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__22_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__23 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__23_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__24 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__24_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lake.CliError.unknownLongOption"};
static const lean_object* l_Lake_instReprCliError_repr___closed__25 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__25_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__25_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__26 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__26_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__26_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__27 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__27_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lake.CliError.unexpectedArguments"};
static const lean_object* l_Lake_instReprCliError_repr___closed__28 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__28_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__28_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__29 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__29_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__30 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__30_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lake.CliError.unknownTemplate"};
static const lean_object* l_Lake_instReprCliError_repr___closed__31 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__31_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__31_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__32 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__32_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__32_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__33 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__33_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lake.CliError.unknownConfigLang"};
static const lean_object* l_Lake_instReprCliError_repr___closed__34 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__34_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__34_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__35 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__35_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__35_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__36 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__36_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.unknownModule"};
static const lean_object* l_Lake_instReprCliError_repr___closed__37 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__37_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__37_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__38 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__38_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__38_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__39 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__39_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lake.CliError.unknownModulePath"};
static const lean_object* l_Lake_instReprCliError_repr___closed__40 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__40_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__40_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__41 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__41_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__41_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__42 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__42_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprCliError_repr___closed__43 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__43_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__43_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__44 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__44_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lake.CliError.unknownPackage"};
static const lean_object* l_Lake_instReprCliError_repr___closed__45 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__45_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__45_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__46 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__46_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__46_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__47 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__47_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lake.CliError.unknownFacet"};
static const lean_object* l_Lake_instReprCliError_repr___closed__48 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__48_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__48_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__49 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__49_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__49_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__50 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__50_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.unknownTarget"};
static const lean_object* l_Lake_instReprCliError_repr___closed__51 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__51_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__51_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__52 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__52_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__52_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__53 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__53_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.missingModule"};
static const lean_object* l_Lake_instReprCliError_repr___closed__54 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__54_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__54_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__55 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__55_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__55_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__56 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__56_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.missingTarget"};
static const lean_object* l_Lake_instReprCliError_repr___closed__57 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__57_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__57_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__58 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__58_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__58_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__59 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__59_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lake.CliError.invalidBuildTarget"};
static const lean_object* l_Lake_instReprCliError_repr___closed__60 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__60_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__60_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__61 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__61_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__61_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__62 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__62_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lake.CliError.invalidTargetSpec"};
static const lean_object* l_Lake_instReprCliError_repr___closed__63 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__63_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__63_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__64 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__64_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__64_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__65 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__65_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lake.CliError.invalidFacet"};
static const lean_object* l_Lake_instReprCliError_repr___closed__66 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__66_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__66_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__67 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__67_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__67_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__68 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__68_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lake.CliError.unknownExe"};
static const lean_object* l_Lake_instReprCliError_repr___closed__69 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__69_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__69_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__70 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__70_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__70_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__71 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__71_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.CliError.unknownScript"};
static const lean_object* l_Lake_instReprCliError_repr___closed__72 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__72_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__72_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__73 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__73_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__73_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__74 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__74_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lake.CliError.missingScriptDoc"};
static const lean_object* l_Lake_instReprCliError_repr___closed__75 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__75_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__75_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__76 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__76_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__76_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__77 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__77_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lake.CliError.invalidScriptSpec"};
static const lean_object* l_Lake_instReprCliError_repr___closed__78 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__78_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__78_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__79 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__79_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__79_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__80 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__80_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lake.CliError.outputConfigExists"};
static const lean_object* l_Lake_instReprCliError_repr___closed__81 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__81_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__81_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__82 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__82_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__82_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__83 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__83_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lake.CliError.leanRevMismatch"};
static const lean_object* l_Lake_instReprCliError_repr___closed__84 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__84_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__84_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__85 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__85_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__85_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__86 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__86_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lake.CliError.invalidEnv"};
static const lean_object* l_Lake_instReprCliError_repr___closed__87 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__87_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__87_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__88 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__88_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__88_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__89 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__89_value;
static const lean_string_object l_Lake_instReprCliError_repr___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lake.CliError.missingRootDir"};
static const lean_object* l_Lake_instReprCliError_repr___closed__90 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__90_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__90_value)}};
static const lean_object* l_Lake_instReprCliError_repr___closed__91 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__91_value;
static const lean_ctor_object l_Lake_instReprCliError_repr___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprCliError_repr___closed__91_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprCliError_repr___closed__92 = (const lean_object*)&l_Lake_instReprCliError_repr___closed__92_value;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_quote(uint32_t);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprCliError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprCliError_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprCliError___closed__0 = (const lean_object*)&l_Lake_instReprCliError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprCliError = (const lean_object*)&l_Lake_instReprCliError___closed__0_value;
static const lean_string_object l_Lake_CliError_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "missing command"};
static const lean_object* l_Lake_CliError_toString___closed__0 = (const lean_object*)&l_Lake_CliError_toString___closed__0_value;
static const lean_string_object l_Lake_CliError_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unknown command '"};
static const lean_object* l_Lake_CliError_toString___closed__1 = (const lean_object*)&l_Lake_CliError_toString___closed__1_value;
static const lean_string_object l_Lake_CliError_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_CliError_toString___closed__2 = (const lean_object*)&l_Lake_CliError_toString___closed__2_value;
static const lean_string_object l_Lake_CliError_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "missing "};
static const lean_object* l_Lake_CliError_toString___closed__3 = (const lean_object*)&l_Lake_CliError_toString___closed__3_value;
static const lean_string_object l_Lake_CliError_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l_Lake_CliError_toString___closed__4 = (const lean_object*)&l_Lake_CliError_toString___closed__4_value;
static const lean_string_object l_Lake_CliError_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid argument for "};
static const lean_object* l_Lake_CliError_toString___closed__5 = (const lean_object*)&l_Lake_CliError_toString___closed__5_value;
static const lean_string_object l_Lake_CliError_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "; expected "};
static const lean_object* l_Lake_CliError_toString___closed__6 = (const lean_object*)&l_Lake_CliError_toString___closed__6_value;
static const lean_string_object l_Lake_CliError_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unknown short option '-"};
static const lean_object* l_Lake_CliError_toString___closed__7 = (const lean_object*)&l_Lake_CliError_toString___closed__7_value;
static const lean_string_object l_Lake_CliError_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_CliError_toString___closed__8 = (const lean_object*)&l_Lake_CliError_toString___closed__8_value;
static const lean_string_object l_Lake_CliError_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown long option '"};
static const lean_object* l_Lake_CliError_toString___closed__9 = (const lean_object*)&l_Lake_CliError_toString___closed__9_value;
static const lean_string_object l_Lake_CliError_toString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unexpected arguments: "};
static const lean_object* l_Lake_CliError_toString___closed__10 = (const lean_object*)&l_Lake_CliError_toString___closed__10_value;
static const lean_string_object l_Lake_CliError_toString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lake_CliError_toString___closed__11 = (const lean_object*)&l_Lake_CliError_toString___closed__11_value;
static const lean_string_object l_Lake_CliError_toString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "the `+` option is an Elan feature; rerun Lake via Elan and ensure this option comes first."};
static const lean_object* l_Lake_CliError_toString___closed__12 = (const lean_object*)&l_Lake_CliError_toString___closed__12_value;
static const lean_string_object l_Lake_CliError_toString___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unknown package template `"};
static const lean_object* l_Lake_CliError_toString___closed__13 = (const lean_object*)&l_Lake_CliError_toString___closed__13_value;
static const lean_string_object l_Lake_CliError_toString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake_CliError_toString___closed__14 = (const lean_object*)&l_Lake_CliError_toString___closed__14_value;
static const lean_string_object l_Lake_CliError_toString___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "unknown configuration language `"};
static const lean_object* l_Lake_CliError_toString___closed__15 = (const lean_object*)&l_Lake_CliError_toString___closed__15_value;
static const lean_string_object l_Lake_CliError_toString___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown module `"};
static const lean_object* l_Lake_CliError_toString___closed__16 = (const lean_object*)&l_Lake_CliError_toString___closed__16_value;
static const lean_string_object l_Lake_CliError_toString___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown module source path `"};
static const lean_object* l_Lake_CliError_toString___closed__17 = (const lean_object*)&l_Lake_CliError_toString___closed__17_value;
static const lean_string_object l_Lake_CliError_toString___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unknown package `"};
static const lean_object* l_Lake_CliError_toString___closed__18 = (const lean_object*)&l_Lake_CliError_toString___closed__18_value;
static const lean_string_object l_Lake_CliError_toString___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unknown "};
static const lean_object* l_Lake_CliError_toString___closed__19 = (const lean_object*)&l_Lake_CliError_toString___closed__19_value;
static const lean_string_object l_Lake_CliError_toString___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " facet `"};
static const lean_object* l_Lake_CliError_toString___closed__20 = (const lean_object*)&l_Lake_CliError_toString___closed__20_value;
static const lean_string_object l_Lake_CliError_toString___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown target `"};
static const lean_object* l_Lake_CliError_toString___closed__21 = (const lean_object*)&l_Lake_CliError_toString___closed__21_value;
static const lean_string_object l_Lake_CliError_toString___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "package '"};
static const lean_object* l_Lake_CliError_toString___closed__22 = (const lean_object*)&l_Lake_CliError_toString___closed__22_value;
static const lean_string_object l_Lake_CliError_toString___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' has no module '"};
static const lean_object* l_Lake_CliError_toString___closed__23 = (const lean_object*)&l_Lake_CliError_toString___closed__23_value;
static const lean_string_object l_Lake_CliError_toString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' has no target '"};
static const lean_object* l_Lake_CliError_toString___closed__24 = (const lean_object*)&l_Lake_CliError_toString___closed__24_value;
static const lean_string_object l_Lake_CliError_toString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "' is not a build target (perhaps you meant 'lake query'\?)"};
static const lean_object* l_Lake_CliError_toString___closed__25 = (const lean_object*)&l_Lake_CliError_toString___closed__25_value;
static const lean_string_object l_Lake_CliError_toString___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid target specifier '"};
static const lean_object* l_Lake_CliError_toString___closed__26 = (const lean_object*)&l_Lake_CliError_toString___closed__26_value;
static const lean_string_object l_Lake_CliError_toString___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "' (too many '"};
static const lean_object* l_Lake_CliError_toString___closed__27 = (const lean_object*)&l_Lake_CliError_toString___closed__27_value;
static const lean_string_object l_Lake_CliError_toString___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l_Lake_CliError_toString___closed__28 = (const lean_object*)&l_Lake_CliError_toString___closed__28_value;
static const lean_string_object l_Lake_CliError_toString___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid facet `"};
static const lean_object* l_Lake_CliError_toString___closed__29 = (const lean_object*)&l_Lake_CliError_toString___closed__29_value;
static const lean_string_object l_Lake_CliError_toString___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`; target "};
static const lean_object* l_Lake_CliError_toString___closed__30 = (const lean_object*)&l_Lake_CliError_toString___closed__30_value;
static const lean_string_object l_Lake_CliError_toString___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " has no facets"};
static const lean_object* l_Lake_CliError_toString___closed__31 = (const lean_object*)&l_Lake_CliError_toString___closed__31_value;
static const lean_string_object l_Lake_CliError_toString___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unknown executable "};
static const lean_object* l_Lake_CliError_toString___closed__32 = (const lean_object*)&l_Lake_CliError_toString___closed__32_value;
static const lean_string_object l_Lake_CliError_toString___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unknown script "};
static const lean_object* l_Lake_CliError_toString___closed__33 = (const lean_object*)&l_Lake_CliError_toString___closed__33_value;
static const lean_string_object l_Lake_CliError_toString___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "no documentation provided for `"};
static const lean_object* l_Lake_CliError_toString___closed__34 = (const lean_object*)&l_Lake_CliError_toString___closed__34_value;
static const lean_string_object l_Lake_CliError_toString___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid script specifier '"};
static const lean_object* l_Lake_CliError_toString___closed__35 = (const lean_object*)&l_Lake_CliError_toString___closed__35_value;
static const lean_string_object l_Lake_CliError_toString___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "' (too many '/')"};
static const lean_object* l_Lake_CliError_toString___closed__36 = (const lean_object*)&l_Lake_CliError_toString___closed__36_value;
static const lean_string_object l_Lake_CliError_toString___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "output configuration file already exists: "};
static const lean_object* l_Lake_CliError_toString___closed__37 = (const lean_object*)&l_Lake_CliError_toString___closed__37_value;
static const lean_string_object l_Lake_CliError_toString___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "could not detect a Lean installation"};
static const lean_object* l_Lake_CliError_toString___closed__38 = (const lean_object*)&l_Lake_CliError_toString___closed__38_value;
static const lean_string_object l_Lake_CliError_toString___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "could not detect the configuration of the Lake installation"};
static const lean_object* l_Lake_CliError_toString___closed__39 = (const lean_object*)&l_Lake_CliError_toString___closed__39_value;
static const lean_string_object l_Lake_CliError_toString___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected Lean commit "};
static const lean_object* l_Lake_CliError_toString___closed__40 = (const lean_object*)&l_Lake_CliError_toString___closed__40_value;
static const lean_string_object l_Lake_CliError_toString___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", but got "};
static const lean_object* l_Lake_CliError_toString___closed__41 = (const lean_object*)&l_Lake_CliError_toString___closed__41_value;
static const lean_string_object l_Lake_CliError_toString___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nothing"};
static const lean_object* l_Lake_CliError_toString___closed__42 = (const lean_object*)&l_Lake_CliError_toString___closed__42_value;
static const lean_string_object l_Lake_CliError_toString___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "workspace directory not found: "};
static const lean_object* l_Lake_CliError_toString___closed__43 = (const lean_object*)&l_Lake_CliError_toString___closed__43_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object*);
static const lean_closure_object l_Lake_CliError_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CliError_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CliError_instToString___closed__0 = (const lean_object*)&l_Lake_CliError_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CliError_instToString = (const lean_object*)&l_Lake_CliError_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
case 11:
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
case 12:
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(12u);
return x_14;
}
case 13:
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(13u);
return x_15;
}
case 14:
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(14u);
return x_16;
}
case 15:
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(15u);
return x_17;
}
case 16:
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(16u);
return x_18;
}
case 17:
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(17u);
return x_19;
}
case 18:
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(18u);
return x_20;
}
case 19:
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(19u);
return x_21;
}
case 20:
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(20u);
return x_22;
}
case 21:
{
lean_object* x_23; 
x_23 = lean_unsigned_to_nat(21u);
return x_23;
}
case 22:
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(22u);
return x_24;
}
case 23:
{
lean_object* x_25; 
x_25 = lean_unsigned_to_nat(23u);
return x_25;
}
case 24:
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(24u);
return x_26;
}
case 25:
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(25u);
return x_27;
}
case 26:
{
lean_object* x_28; 
x_28 = lean_unsigned_to_nat(26u);
return x_28;
}
case 27:
{
lean_object* x_29; 
x_29 = lean_unsigned_to_nat(27u);
return x_29;
}
case 28:
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(28u);
return x_30;
}
case 29:
{
lean_object* x_31; 
x_31 = lean_unsigned_to_nat(29u);
return x_31;
}
default: 
{
lean_object* x_32; 
x_32 = lean_unsigned_to_nat(30u);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_CliError_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
case 5:
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_1(x_2, x_16);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec_ref(x_1);
x_19 = lean_apply_1(x_2, x_18);
return x_19;
}
case 9:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_apply_1(x_2, x_20);
return x_21;
}
case 10:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_1(x_2, x_22);
return x_23;
}
case 11:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec_ref(x_1);
x_25 = lean_apply_1(x_2, x_24);
return x_25;
}
case 12:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_apply_1(x_2, x_26);
return x_27;
}
case 13:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_apply_1(x_2, x_28);
return x_29;
}
case 14:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_apply_2(x_2, x_30, x_31);
return x_32;
}
case 15:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = lean_apply_1(x_2, x_33);
return x_34;
}
case 16:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec_ref(x_1);
x_37 = lean_apply_2(x_2, x_35, x_36);
return x_37;
}
case 17:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
x_40 = lean_apply_2(x_2, x_38, x_39);
return x_40;
}
case 18:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_41);
lean_dec_ref(x_1);
x_42 = lean_apply_1(x_2, x_41);
return x_42;
}
case 19:
{
lean_object* x_43; uint32_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_45 = lean_box_uint32(x_44);
x_46 = lean_apply_2(x_2, x_43, x_45);
return x_46;
}
case 20:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec_ref(x_1);
x_49 = lean_apply_2(x_2, x_47, x_48);
return x_49;
}
case 21:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_51 = lean_apply_1(x_2, x_50);
return x_51;
}
case 22:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_apply_1(x_2, x_52);
return x_53;
}
case 23:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_1);
x_55 = lean_apply_1(x_2, x_54);
return x_55;
}
case 24:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_56);
lean_dec_ref(x_1);
x_57 = lean_apply_1(x_2, x_56);
return x_57;
}
case 25:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_58);
lean_dec_ref(x_1);
x_59 = lean_apply_1(x_2, x_58);
return x_59;
}
case 28:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_61);
lean_dec_ref(x_1);
x_62 = lean_apply_2(x_2, x_60, x_61);
return x_62;
}
case 29:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_63);
lean_dec_ref(x_1);
x_64 = lean_apply_1(x_2, x_63);
return x_64;
}
case 30:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_65);
lean_dec_ref(x_1);
x_66 = lean_apply_1(x_2, x_65);
return x_66;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_CliError_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_CliError_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CliError_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CliError_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_quote(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_6 = x_3;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; 
lean_inc(x_1);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_2);
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_String_quote(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_2 = x_11;
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_6 = x_3;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; 
lean_inc(x_1);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_2);
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_String_quote(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(x_1, x_11, x_5);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1));
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5));
x_4 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(x_1, x_3);
x_5 = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8);
x_6 = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9));
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10));
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Std_Format_fill(x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_17 = x_33;
goto block_23;
}
else
{
lean_object* x_34; 
x_34 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_17 = x_34;
goto block_23;
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_55; 
x_35 = lean_ctor_get(x_1, 0);
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
x_36 = x_1;
x_37 = x_55;
goto block_54;
}
else
{
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_38; lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_38 = x_52;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_38 = x_53;
goto block_49;
}
block_49:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__12));
x_40 = l_String_quote(x_35);
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_40);
x_41 = x_36;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_40);
x_41 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = 0;
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = l_Repr_addAppParen(x_45, x_2);
return x_46;
}
}
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_76; 
x_56 = lean_ctor_get(x_1, 0);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
x_57 = x_1;
x_58 = x_76;
goto block_75;
}
else
{
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_59; lean_object* x_71; uint8_t x_72; 
x_71 = lean_unsigned_to_nat(1024u);
x_72 = lean_nat_dec_le(x_71, x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_59 = x_73;
goto block_70;
}
else
{
lean_object* x_74; 
x_74 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_59 = x_74;
goto block_70;
}
block_70:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__15));
x_61 = l_String_quote(x_56);
if (x_58 == 0)
{
lean_ctor_set_tag(x_57, 3);
lean_ctor_set(x_57, 0, x_61);
x_62 = x_57;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_62 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = 0;
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = l_Repr_addAppParen(x_66, x_2);
return x_67;
}
}
}
}
case 3:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_103; 
x_77 = lean_ctor_get(x_1, 0);
x_78 = lean_ctor_get(x_1, 1);
x_103 = !lean_is_exclusive(x_1);
if (x_103 == 0)
{
x_79 = x_1;
x_80 = x_103;
goto block_102;
}
else
{
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_81; lean_object* x_98; uint8_t x_99; 
x_98 = lean_unsigned_to_nat(1024u);
x_99 = lean_nat_dec_le(x_98, x_2);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_81 = x_100;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_81 = x_101;
goto block_97;
}
block_97:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_box(1);
x_83 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__18));
x_84 = l_String_quote(x_77);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (x_80 == 0)
{
lean_ctor_set_tag(x_79, 5);
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_83);
x_86 = x_79;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_85);
x_86 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
x_88 = l_String_quote(x_78);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_92 = 0;
x_93 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = l_Repr_addAppParen(x_93, x_2);
return x_94;
}
}
}
}
case 4:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_130; 
x_104 = lean_ctor_get(x_1, 0);
x_105 = lean_ctor_get(x_1, 1);
x_130 = !lean_is_exclusive(x_1);
if (x_130 == 0)
{
x_106 = x_1;
x_107 = x_130;
goto block_129;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_1);
x_106 = lean_box(0);
x_107 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_108; lean_object* x_125; uint8_t x_126; 
x_125 = lean_unsigned_to_nat(1024u);
x_126 = lean_nat_dec_le(x_125, x_2);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_108 = x_127;
goto block_124;
}
else
{
lean_object* x_128; 
x_128 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_108 = x_128;
goto block_124;
}
block_124:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_box(1);
x_110 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__21));
x_111 = l_String_quote(x_104);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (x_107 == 0)
{
lean_ctor_set_tag(x_106, 5);
lean_ctor_set(x_106, 1, x_112);
lean_ctor_set(x_106, 0, x_110);
x_113 = x_106;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_112);
x_113 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
x_115 = l_String_quote(x_105);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_117);
x_119 = 0;
x_120 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = l_Repr_addAppParen(x_120, x_2);
return x_121;
}
}
}
}
case 5:
{
uint32_t x_131; lean_object* x_132; lean_object* x_142; uint8_t x_143; 
x_131 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_142 = lean_unsigned_to_nat(1024u);
x_143 = lean_nat_dec_le(x_142, x_2);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_132 = x_144;
goto block_141;
}
else
{
lean_object* x_145; 
x_145 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_132 = x_145;
goto block_141;
}
block_141:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_133 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__24));
x_134 = l_Char_quote(x_131);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
x_138 = 0;
x_139 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = l_Repr_addAppParen(x_139, x_2);
return x_140;
}
}
case 6:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_166; 
x_146 = lean_ctor_get(x_1, 0);
x_166 = !lean_is_exclusive(x_1);
if (x_166 == 0)
{
x_147 = x_1;
x_148 = x_166;
goto block_165;
}
else
{
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_box(0);
x_148 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_149; lean_object* x_161; uint8_t x_162; 
x_161 = lean_unsigned_to_nat(1024u);
x_162 = lean_nat_dec_le(x_161, x_2);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_149 = x_163;
goto block_160;
}
else
{
lean_object* x_164; 
x_164 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_149 = x_164;
goto block_160;
}
block_160:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__27));
x_151 = l_String_quote(x_146);
if (x_148 == 0)
{
lean_ctor_set_tag(x_147, 3);
lean_ctor_set(x_147, 0, x_151);
x_152 = x_147;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_159, 0, x_151);
x_152 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_153);
x_155 = 0;
x_156 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = l_Repr_addAppParen(x_156, x_2);
return x_157;
}
}
}
}
case 7:
{
lean_object* x_167; lean_object* x_168; lean_object* x_177; uint8_t x_178; 
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
lean_dec_ref(x_1);
x_177 = lean_unsigned_to_nat(1024u);
x_178 = lean_nat_dec_le(x_177, x_2);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_168 = x_179;
goto block_176;
}
else
{
lean_object* x_180; 
x_180 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_168 = x_180;
goto block_176;
}
block_176:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_169 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__30));
x_170 = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(x_167);
x_171 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = 0;
x_174 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = l_Repr_addAppParen(x_174, x_2);
return x_175;
}
}
case 8:
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_unsigned_to_nat(1024u);
x_182 = lean_nat_dec_le(x_181, x_2);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_24 = x_183;
goto block_30;
}
else
{
lean_object* x_184; 
x_184 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_24 = x_184;
goto block_30;
}
}
case 9:
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_205; 
x_185 = lean_ctor_get(x_1, 0);
x_205 = !lean_is_exclusive(x_1);
if (x_205 == 0)
{
x_186 = x_1;
x_187 = x_205;
goto block_204;
}
else
{
lean_inc(x_185);
lean_dec(x_1);
x_186 = lean_box(0);
x_187 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_188; lean_object* x_200; uint8_t x_201; 
x_200 = lean_unsigned_to_nat(1024u);
x_201 = lean_nat_dec_le(x_200, x_2);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_188 = x_202;
goto block_199;
}
else
{
lean_object* x_203; 
x_203 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_188 = x_203;
goto block_199;
}
block_199:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__33));
x_190 = l_String_quote(x_185);
if (x_187 == 0)
{
lean_ctor_set_tag(x_186, 3);
lean_ctor_set(x_186, 0, x_190);
x_191 = x_186;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_198, 0, x_190);
x_191 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
x_194 = 0;
x_195 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = l_Repr_addAppParen(x_195, x_2);
return x_196;
}
}
}
}
case 10:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; uint8_t x_226; 
x_206 = lean_ctor_get(x_1, 0);
x_226 = !lean_is_exclusive(x_1);
if (x_226 == 0)
{
x_207 = x_1;
x_208 = x_226;
goto block_225;
}
else
{
lean_inc(x_206);
lean_dec(x_1);
x_207 = lean_box(0);
x_208 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_209; lean_object* x_221; uint8_t x_222; 
x_221 = lean_unsigned_to_nat(1024u);
x_222 = lean_nat_dec_le(x_221, x_2);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_209 = x_223;
goto block_220;
}
else
{
lean_object* x_224; 
x_224 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_209 = x_224;
goto block_220;
}
block_220:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__36));
x_211 = l_String_quote(x_206);
if (x_208 == 0)
{
lean_ctor_set_tag(x_207, 3);
lean_ctor_set(x_207, 0, x_211);
x_212 = x_207;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_219, 0, x_211);
x_212 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_213);
x_215 = 0;
x_216 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set_uint8(x_216, sizeof(void*)*1, x_215);
x_217 = l_Repr_addAppParen(x_216, x_2);
return x_217;
}
}
}
}
case 11:
{
lean_object* x_227; lean_object* x_228; lean_object* x_238; uint8_t x_239; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
lean_dec_ref(x_1);
x_238 = lean_unsigned_to_nat(1024u);
x_239 = lean_nat_dec_le(x_238, x_2);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_228 = x_240;
goto block_237;
}
else
{
lean_object* x_241; 
x_241 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_228 = x_241;
goto block_237;
}
block_237:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; 
x_229 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__39));
x_230 = lean_unsigned_to_nat(1024u);
x_231 = l_Lean_Name_reprPrec(x_227, x_230);
x_232 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_233, 0, x_228);
lean_ctor_set(x_233, 1, x_232);
x_234 = 0;
x_235 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_234);
x_236 = l_Repr_addAppParen(x_235, x_2);
return x_236;
}
}
case 12:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_266; 
x_242 = lean_ctor_get(x_1, 0);
x_266 = !lean_is_exclusive(x_1);
if (x_266 == 0)
{
x_243 = x_1;
x_244 = x_266;
goto block_265;
}
else
{
lean_inc(x_242);
lean_dec(x_1);
x_243 = lean_box(0);
x_244 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_245; lean_object* x_261; uint8_t x_262; 
x_261 = lean_unsigned_to_nat(1024u);
x_262 = lean_nat_dec_le(x_261, x_2);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_245 = x_263;
goto block_260;
}
else
{
lean_object* x_264; 
x_264 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_245 = x_264;
goto block_260;
}
block_260:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__42));
x_247 = lean_unsigned_to_nat(1024u);
x_248 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
x_249 = l_String_quote(x_242);
if (x_244 == 0)
{
lean_ctor_set_tag(x_243, 3);
lean_ctor_set(x_243, 0, x_249);
x_250 = x_243;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_249);
x_250 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Repr_addAppParen(x_251, x_247);
x_253 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_254, 0, x_245);
lean_ctor_set(x_254, 1, x_253);
x_255 = 0;
x_256 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*1, x_255);
x_257 = l_Repr_addAppParen(x_256, x_2);
return x_257;
}
}
}
}
case 13:
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_287; 
x_267 = lean_ctor_get(x_1, 0);
x_287 = !lean_is_exclusive(x_1);
if (x_287 == 0)
{
x_268 = x_1;
x_269 = x_287;
goto block_286;
}
else
{
lean_inc(x_267);
lean_dec(x_1);
x_268 = lean_box(0);
x_269 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_270; lean_object* x_282; uint8_t x_283; 
x_282 = lean_unsigned_to_nat(1024u);
x_283 = lean_nat_dec_le(x_282, x_2);
if (x_283 == 0)
{
lean_object* x_284; 
x_284 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_270 = x_284;
goto block_281;
}
else
{
lean_object* x_285; 
x_285 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_270 = x_285;
goto block_281;
}
block_281:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__47));
x_272 = l_String_quote(x_267);
if (x_269 == 0)
{
lean_ctor_set_tag(x_268, 3);
lean_ctor_set(x_268, 0, x_272);
x_273 = x_268;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_280, 0, x_272);
x_273 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_275, 0, x_270);
lean_ctor_set(x_275, 1, x_274);
x_276 = 0;
x_277 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*1, x_276);
x_278 = l_Repr_addAppParen(x_277, x_2);
return x_278;
}
}
}
}
case 14:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_314; 
x_288 = lean_ctor_get(x_1, 0);
x_289 = lean_ctor_get(x_1, 1);
x_314 = !lean_is_exclusive(x_1);
if (x_314 == 0)
{
x_290 = x_1;
x_291 = x_314;
goto block_313;
}
else
{
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_1);
x_290 = lean_box(0);
x_291 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_292; lean_object* x_309; uint8_t x_310; 
x_309 = lean_unsigned_to_nat(1024u);
x_310 = lean_nat_dec_le(x_309, x_2);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_292 = x_311;
goto block_308;
}
else
{
lean_object* x_312; 
x_312 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_292 = x_312;
goto block_308;
}
block_308:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_box(1);
x_294 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__50));
x_295 = l_String_quote(x_288);
x_296 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_296, 0, x_295);
if (x_291 == 0)
{
lean_ctor_set_tag(x_290, 5);
lean_ctor_set(x_290, 1, x_296);
lean_ctor_set(x_290, 0, x_294);
x_297 = x_290;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_307, 0, x_294);
lean_ctor_set(x_307, 1, x_296);
x_297 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; 
x_298 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_293);
x_299 = lean_unsigned_to_nat(1024u);
x_300 = l_Lean_Name_reprPrec(x_289, x_299);
x_301 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_302, 0, x_292);
lean_ctor_set(x_302, 1, x_301);
x_303 = 0;
x_304 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_303);
x_305 = l_Repr_addAppParen(x_304, x_2);
return x_305;
}
}
}
}
case 15:
{
lean_object* x_315; lean_object* x_316; lean_object* x_326; uint8_t x_327; 
x_315 = lean_ctor_get(x_1, 0);
lean_inc(x_315);
lean_dec_ref(x_1);
x_326 = lean_unsigned_to_nat(1024u);
x_327 = lean_nat_dec_le(x_326, x_2);
if (x_327 == 0)
{
lean_object* x_328; 
x_328 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_316 = x_328;
goto block_325;
}
else
{
lean_object* x_329; 
x_329 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_316 = x_329;
goto block_325;
}
block_325:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; 
x_317 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__53));
x_318 = lean_unsigned_to_nat(1024u);
x_319 = l_Lean_Name_reprPrec(x_315, x_318);
x_320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_321, 0, x_316);
lean_ctor_set(x_321, 1, x_320);
x_322 = 0;
x_323 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*1, x_322);
x_324 = l_Repr_addAppParen(x_323, x_2);
return x_324;
}
}
case 16:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_355; 
x_330 = lean_ctor_get(x_1, 0);
x_331 = lean_ctor_get(x_1, 1);
x_355 = !lean_is_exclusive(x_1);
if (x_355 == 0)
{
x_332 = x_1;
x_333 = x_355;
goto block_354;
}
else
{
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_1);
x_332 = lean_box(0);
x_333 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_334; lean_object* x_350; uint8_t x_351; 
x_350 = lean_unsigned_to_nat(1024u);
x_351 = lean_nat_dec_le(x_350, x_2);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_334 = x_352;
goto block_349;
}
else
{
lean_object* x_353; 
x_353 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_334 = x_353;
goto block_349;
}
block_349:
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_box(1);
x_336 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__56));
x_337 = lean_unsigned_to_nat(1024u);
x_338 = l_Lean_Name_reprPrec(x_330, x_337);
if (x_333 == 0)
{
lean_ctor_set_tag(x_332, 5);
lean_ctor_set(x_332, 1, x_338);
lean_ctor_set(x_332, 0, x_336);
x_339 = x_332;
goto block_347;
}
else
{
lean_object* x_348; 
x_348 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_338);
x_339 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; 
x_340 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_335);
x_341 = l_Lean_Name_reprPrec(x_331, x_337);
x_342 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_343, 0, x_334);
lean_ctor_set(x_343, 1, x_342);
x_344 = 0;
x_345 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_344);
x_346 = l_Repr_addAppParen(x_345, x_2);
return x_346;
}
}
}
}
case 17:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; uint8_t x_382; 
x_356 = lean_ctor_get(x_1, 0);
x_357 = lean_ctor_get(x_1, 1);
x_382 = !lean_is_exclusive(x_1);
if (x_382 == 0)
{
x_358 = x_1;
x_359 = x_382;
goto block_381;
}
else
{
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_1);
x_358 = lean_box(0);
x_359 = x_382;
goto block_381;
}
block_381:
{
lean_object* x_360; lean_object* x_377; uint8_t x_378; 
x_377 = lean_unsigned_to_nat(1024u);
x_378 = lean_nat_dec_le(x_377, x_2);
if (x_378 == 0)
{
lean_object* x_379; 
x_379 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_360 = x_379;
goto block_376;
}
else
{
lean_object* x_380; 
x_380 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_360 = x_380;
goto block_376;
}
block_376:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_361 = lean_box(1);
x_362 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__59));
x_363 = lean_unsigned_to_nat(1024u);
x_364 = l_Lean_Name_reprPrec(x_356, x_363);
if (x_359 == 0)
{
lean_ctor_set_tag(x_358, 5);
lean_ctor_set(x_358, 1, x_364);
lean_ctor_set(x_358, 0, x_362);
x_365 = x_358;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_375, 0, x_362);
lean_ctor_set(x_375, 1, x_364);
x_365 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; 
x_366 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_361);
x_367 = l_String_quote(x_357);
x_368 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_370, 0, x_360);
lean_ctor_set(x_370, 1, x_369);
x_371 = 0;
x_372 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*1, x_371);
x_373 = l_Repr_addAppParen(x_372, x_2);
return x_373;
}
}
}
}
case 18:
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; uint8_t x_403; 
x_383 = lean_ctor_get(x_1, 0);
x_403 = !lean_is_exclusive(x_1);
if (x_403 == 0)
{
x_384 = x_1;
x_385 = x_403;
goto block_402;
}
else
{
lean_inc(x_383);
lean_dec(x_1);
x_384 = lean_box(0);
x_385 = x_403;
goto block_402;
}
block_402:
{
lean_object* x_386; lean_object* x_398; uint8_t x_399; 
x_398 = lean_unsigned_to_nat(1024u);
x_399 = lean_nat_dec_le(x_398, x_2);
if (x_399 == 0)
{
lean_object* x_400; 
x_400 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_386 = x_400;
goto block_397;
}
else
{
lean_object* x_401; 
x_401 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_386 = x_401;
goto block_397;
}
block_397:
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__62));
x_388 = l_String_quote(x_383);
if (x_385 == 0)
{
lean_ctor_set_tag(x_384, 3);
lean_ctor_set(x_384, 0, x_388);
x_389 = x_384;
goto block_395;
}
else
{
lean_object* x_396; 
x_396 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_396, 0, x_388);
x_389 = x_396;
goto block_395;
}
block_395:
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_391, 0, x_386);
lean_ctor_set(x_391, 1, x_390);
x_392 = 0;
x_393 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_392);
x_394 = l_Repr_addAppParen(x_393, x_2);
return x_394;
}
}
}
}
case 19:
{
lean_object* x_404; uint32_t x_405; lean_object* x_406; lean_object* x_421; uint8_t x_422; 
x_404 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_404);
x_405 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_421 = lean_unsigned_to_nat(1024u);
x_422 = lean_nat_dec_le(x_421, x_2);
if (x_422 == 0)
{
lean_object* x_423; 
x_423 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_406 = x_423;
goto block_420;
}
else
{
lean_object* x_424; 
x_424 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_406 = x_424;
goto block_420;
}
block_420:
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; 
x_407 = lean_box(1);
x_408 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__65));
x_409 = l_String_quote(x_404);
x_410 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_407);
x_413 = l_Char_quote(x_405);
x_414 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_415 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_416, 0, x_406);
lean_ctor_set(x_416, 1, x_415);
x_417 = 0;
x_418 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set_uint8(x_418, sizeof(void*)*1, x_417);
x_419 = l_Repr_addAppParen(x_418, x_2);
return x_419;
}
}
case 20:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_450; 
x_425 = lean_ctor_get(x_1, 0);
x_426 = lean_ctor_get(x_1, 1);
x_450 = !lean_is_exclusive(x_1);
if (x_450 == 0)
{
x_427 = x_1;
x_428 = x_450;
goto block_449;
}
else
{
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_1);
x_427 = lean_box(0);
x_428 = x_450;
goto block_449;
}
block_449:
{
lean_object* x_429; lean_object* x_445; uint8_t x_446; 
x_445 = lean_unsigned_to_nat(1024u);
x_446 = lean_nat_dec_le(x_445, x_2);
if (x_446 == 0)
{
lean_object* x_447; 
x_447 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_429 = x_447;
goto block_444;
}
else
{
lean_object* x_448; 
x_448 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_429 = x_448;
goto block_444;
}
block_444:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_box(1);
x_431 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__68));
x_432 = lean_unsigned_to_nat(1024u);
x_433 = l_Lean_Name_reprPrec(x_425, x_432);
if (x_428 == 0)
{
lean_ctor_set_tag(x_427, 5);
lean_ctor_set(x_427, 1, x_433);
lean_ctor_set(x_427, 0, x_431);
x_434 = x_427;
goto block_442;
}
else
{
lean_object* x_443; 
x_443 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_443, 0, x_431);
lean_ctor_set(x_443, 1, x_433);
x_434 = x_443;
goto block_442;
}
block_442:
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; 
x_435 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_430);
x_436 = l_Lean_Name_reprPrec(x_426, x_432);
x_437 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_438, 0, x_429);
lean_ctor_set(x_438, 1, x_437);
x_439 = 0;
x_440 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set_uint8(x_440, sizeof(void*)*1, x_439);
x_441 = l_Repr_addAppParen(x_440, x_2);
return x_441;
}
}
}
}
case 21:
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; uint8_t x_471; 
x_451 = lean_ctor_get(x_1, 0);
x_471 = !lean_is_exclusive(x_1);
if (x_471 == 0)
{
x_452 = x_1;
x_453 = x_471;
goto block_470;
}
else
{
lean_inc(x_451);
lean_dec(x_1);
x_452 = lean_box(0);
x_453 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_454; lean_object* x_466; uint8_t x_467; 
x_466 = lean_unsigned_to_nat(1024u);
x_467 = lean_nat_dec_le(x_466, x_2);
if (x_467 == 0)
{
lean_object* x_468; 
x_468 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_454 = x_468;
goto block_465;
}
else
{
lean_object* x_469; 
x_469 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_454 = x_469;
goto block_465;
}
block_465:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__71));
x_456 = l_String_quote(x_451);
if (x_453 == 0)
{
lean_ctor_set_tag(x_452, 3);
lean_ctor_set(x_452, 0, x_456);
x_457 = x_452;
goto block_463;
}
else
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_464, 0, x_456);
x_457 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; 
x_458 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_459, 0, x_454);
lean_ctor_set(x_459, 1, x_458);
x_460 = 0;
x_461 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set_uint8(x_461, sizeof(void*)*1, x_460);
x_462 = l_Repr_addAppParen(x_461, x_2);
return x_462;
}
}
}
}
case 22:
{
lean_object* x_472; lean_object* x_473; uint8_t x_474; uint8_t x_492; 
x_472 = lean_ctor_get(x_1, 0);
x_492 = !lean_is_exclusive(x_1);
if (x_492 == 0)
{
x_473 = x_1;
x_474 = x_492;
goto block_491;
}
else
{
lean_inc(x_472);
lean_dec(x_1);
x_473 = lean_box(0);
x_474 = x_492;
goto block_491;
}
block_491:
{
lean_object* x_475; lean_object* x_487; uint8_t x_488; 
x_487 = lean_unsigned_to_nat(1024u);
x_488 = lean_nat_dec_le(x_487, x_2);
if (x_488 == 0)
{
lean_object* x_489; 
x_489 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_475 = x_489;
goto block_486;
}
else
{
lean_object* x_490; 
x_490 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_475 = x_490;
goto block_486;
}
block_486:
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__74));
x_477 = l_String_quote(x_472);
if (x_474 == 0)
{
lean_ctor_set_tag(x_473, 3);
lean_ctor_set(x_473, 0, x_477);
x_478 = x_473;
goto block_484;
}
else
{
lean_object* x_485; 
x_485 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_485, 0, x_477);
x_478 = x_485;
goto block_484;
}
block_484:
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; 
x_479 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_480, 0, x_475);
lean_ctor_set(x_480, 1, x_479);
x_481 = 0;
x_482 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*1, x_481);
x_483 = l_Repr_addAppParen(x_482, x_2);
return x_483;
}
}
}
}
case 23:
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; uint8_t x_513; 
x_493 = lean_ctor_get(x_1, 0);
x_513 = !lean_is_exclusive(x_1);
if (x_513 == 0)
{
x_494 = x_1;
x_495 = x_513;
goto block_512;
}
else
{
lean_inc(x_493);
lean_dec(x_1);
x_494 = lean_box(0);
x_495 = x_513;
goto block_512;
}
block_512:
{
lean_object* x_496; lean_object* x_508; uint8_t x_509; 
x_508 = lean_unsigned_to_nat(1024u);
x_509 = lean_nat_dec_le(x_508, x_2);
if (x_509 == 0)
{
lean_object* x_510; 
x_510 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_496 = x_510;
goto block_507;
}
else
{
lean_object* x_511; 
x_511 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_496 = x_511;
goto block_507;
}
block_507:
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__77));
x_498 = l_String_quote(x_493);
if (x_495 == 0)
{
lean_ctor_set_tag(x_494, 3);
lean_ctor_set(x_494, 0, x_498);
x_499 = x_494;
goto block_505;
}
else
{
lean_object* x_506; 
x_506 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_506, 0, x_498);
x_499 = x_506;
goto block_505;
}
block_505:
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_501, 0, x_496);
lean_ctor_set(x_501, 1, x_500);
x_502 = 0;
x_503 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_503, 0, x_501);
lean_ctor_set_uint8(x_503, sizeof(void*)*1, x_502);
x_504 = l_Repr_addAppParen(x_503, x_2);
return x_504;
}
}
}
}
case 24:
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; uint8_t x_534; 
x_514 = lean_ctor_get(x_1, 0);
x_534 = !lean_is_exclusive(x_1);
if (x_534 == 0)
{
x_515 = x_1;
x_516 = x_534;
goto block_533;
}
else
{
lean_inc(x_514);
lean_dec(x_1);
x_515 = lean_box(0);
x_516 = x_534;
goto block_533;
}
block_533:
{
lean_object* x_517; lean_object* x_529; uint8_t x_530; 
x_529 = lean_unsigned_to_nat(1024u);
x_530 = lean_nat_dec_le(x_529, x_2);
if (x_530 == 0)
{
lean_object* x_531; 
x_531 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_517 = x_531;
goto block_528;
}
else
{
lean_object* x_532; 
x_532 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_517 = x_532;
goto block_528;
}
block_528:
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__80));
x_519 = l_String_quote(x_514);
if (x_516 == 0)
{
lean_ctor_set_tag(x_515, 3);
lean_ctor_set(x_515, 0, x_519);
x_520 = x_515;
goto block_526;
}
else
{
lean_object* x_527; 
x_527 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_527, 0, x_519);
x_520 = x_527;
goto block_526;
}
block_526:
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; 
x_521 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_520);
x_522 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_522, 0, x_517);
lean_ctor_set(x_522, 1, x_521);
x_523 = 0;
x_524 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set_uint8(x_524, sizeof(void*)*1, x_523);
x_525 = l_Repr_addAppParen(x_524, x_2);
return x_525;
}
}
}
}
case 25:
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; uint8_t x_559; 
x_535 = lean_ctor_get(x_1, 0);
x_559 = !lean_is_exclusive(x_1);
if (x_559 == 0)
{
x_536 = x_1;
x_537 = x_559;
goto block_558;
}
else
{
lean_inc(x_535);
lean_dec(x_1);
x_536 = lean_box(0);
x_537 = x_559;
goto block_558;
}
block_558:
{
lean_object* x_538; lean_object* x_554; uint8_t x_555; 
x_554 = lean_unsigned_to_nat(1024u);
x_555 = lean_nat_dec_le(x_554, x_2);
if (x_555 == 0)
{
lean_object* x_556; 
x_556 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_538 = x_556;
goto block_553;
}
else
{
lean_object* x_557; 
x_557 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_538 = x_557;
goto block_553;
}
block_553:
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_539 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__83));
x_540 = lean_unsigned_to_nat(1024u);
x_541 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
x_542 = l_String_quote(x_535);
if (x_537 == 0)
{
lean_ctor_set_tag(x_536, 3);
lean_ctor_set(x_536, 0, x_542);
x_543 = x_536;
goto block_551;
}
else
{
lean_object* x_552; 
x_552 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_552, 0, x_542);
x_543 = x_552;
goto block_551;
}
block_551:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; lean_object* x_549; lean_object* x_550; 
x_544 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Repr_addAppParen(x_544, x_540);
x_546 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_546, 0, x_539);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_547, 0, x_538);
lean_ctor_set(x_547, 1, x_546);
x_548 = 0;
x_549 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set_uint8(x_549, sizeof(void*)*1, x_548);
x_550 = l_Repr_addAppParen(x_549, x_2);
return x_550;
}
}
}
}
case 26:
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_unsigned_to_nat(1024u);
x_561 = lean_nat_dec_le(x_560, x_2);
if (x_561 == 0)
{
lean_object* x_562; 
x_562 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_10 = x_562;
goto block_16;
}
else
{
lean_object* x_563; 
x_563 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_10 = x_563;
goto block_16;
}
}
case 27:
{
lean_object* x_564; uint8_t x_565; 
x_564 = lean_unsigned_to_nat(1024u);
x_565 = lean_nat_dec_le(x_564, x_2);
if (x_565 == 0)
{
lean_object* x_566; 
x_566 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_3 = x_566;
goto block_9;
}
else
{
lean_object* x_567; 
x_567 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_3 = x_567;
goto block_9;
}
}
case 28:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; uint8_t x_594; 
x_568 = lean_ctor_get(x_1, 0);
x_569 = lean_ctor_get(x_1, 1);
x_594 = !lean_is_exclusive(x_1);
if (x_594 == 0)
{
x_570 = x_1;
x_571 = x_594;
goto block_593;
}
else
{
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_1);
x_570 = lean_box(0);
x_571 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_572; lean_object* x_589; uint8_t x_590; 
x_589 = lean_unsigned_to_nat(1024u);
x_590 = lean_nat_dec_le(x_589, x_2);
if (x_590 == 0)
{
lean_object* x_591; 
x_591 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_572 = x_591;
goto block_588;
}
else
{
lean_object* x_592; 
x_592 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_572 = x_592;
goto block_588;
}
block_588:
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_573 = lean_box(1);
x_574 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__86));
x_575 = l_String_quote(x_568);
x_576 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_576, 0, x_575);
if (x_571 == 0)
{
lean_ctor_set_tag(x_570, 5);
lean_ctor_set(x_570, 1, x_576);
lean_ctor_set(x_570, 0, x_574);
x_577 = x_570;
goto block_586;
}
else
{
lean_object* x_587; 
x_587 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_587, 0, x_574);
lean_ctor_set(x_587, 1, x_576);
x_577 = x_587;
goto block_586;
}
block_586:
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; 
x_578 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_573);
x_579 = l_String_quote(x_569);
x_580 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_580, 0, x_579);
x_581 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_582, 0, x_572);
lean_ctor_set(x_582, 1, x_581);
x_583 = 0;
x_584 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set_uint8(x_584, sizeof(void*)*1, x_583);
x_585 = l_Repr_addAppParen(x_584, x_2);
return x_585;
}
}
}
}
case 29:
{
lean_object* x_595; lean_object* x_596; uint8_t x_597; uint8_t x_615; 
x_595 = lean_ctor_get(x_1, 0);
x_615 = !lean_is_exclusive(x_1);
if (x_615 == 0)
{
x_596 = x_1;
x_597 = x_615;
goto block_614;
}
else
{
lean_inc(x_595);
lean_dec(x_1);
x_596 = lean_box(0);
x_597 = x_615;
goto block_614;
}
block_614:
{
lean_object* x_598; lean_object* x_610; uint8_t x_611; 
x_610 = lean_unsigned_to_nat(1024u);
x_611 = lean_nat_dec_le(x_610, x_2);
if (x_611 == 0)
{
lean_object* x_612; 
x_612 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_598 = x_612;
goto block_609;
}
else
{
lean_object* x_613; 
x_613 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_598 = x_613;
goto block_609;
}
block_609:
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__89));
x_600 = l_String_quote(x_595);
if (x_597 == 0)
{
lean_ctor_set_tag(x_596, 3);
lean_ctor_set(x_596, 0, x_600);
x_601 = x_596;
goto block_607;
}
else
{
lean_object* x_608; 
x_608 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_608, 0, x_600);
x_601 = x_608;
goto block_607;
}
block_607:
{
lean_object* x_602; lean_object* x_603; uint8_t x_604; lean_object* x_605; lean_object* x_606; 
x_602 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_601);
x_603 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_603, 0, x_598);
lean_ctor_set(x_603, 1, x_602);
x_604 = 0;
x_605 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set_uint8(x_605, sizeof(void*)*1, x_604);
x_606 = l_Repr_addAppParen(x_605, x_2);
return x_606;
}
}
}
}
default: 
{
lean_object* x_616; lean_object* x_617; uint8_t x_618; uint8_t x_640; 
x_616 = lean_ctor_get(x_1, 0);
x_640 = !lean_is_exclusive(x_1);
if (x_640 == 0)
{
x_617 = x_1;
x_618 = x_640;
goto block_639;
}
else
{
lean_inc(x_616);
lean_dec(x_1);
x_617 = lean_box(0);
x_618 = x_640;
goto block_639;
}
block_639:
{
lean_object* x_619; lean_object* x_635; uint8_t x_636; 
x_635 = lean_unsigned_to_nat(1024u);
x_636 = lean_nat_dec_le(x_635, x_2);
if (x_636 == 0)
{
lean_object* x_637; 
x_637 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
x_619 = x_637;
goto block_634;
}
else
{
lean_object* x_638; 
x_638 = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
x_619 = x_638;
goto block_634;
}
block_634:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__92));
x_621 = lean_unsigned_to_nat(1024u);
x_622 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
x_623 = l_String_quote(x_616);
if (x_618 == 0)
{
lean_ctor_set_tag(x_617, 3);
lean_ctor_set(x_617, 0, x_623);
x_624 = x_617;
goto block_632;
}
else
{
lean_object* x_633; 
x_633 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_633, 0, x_623);
x_624 = x_633;
goto block_632;
}
block_632:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; 
x_625 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_624);
x_626 = l_Repr_addAppParen(x_625, x_621);
x_627 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_627, 0, x_620);
lean_ctor_set(x_627, 1, x_626);
x_628 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_628, 0, x_619);
lean_ctor_set(x_628, 1, x_627);
x_629 = 0;
x_630 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set_uint8(x_630, sizeof(void*)*1, x_629);
x_631 = l_Repr_addAppParen(x_630, x_2);
return x_631;
}
}
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__5));
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = ((lean_object*)(l_Lake_instReprCliError_repr___closed__7));
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprCliError_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lake_CliError_toString___closed__0));
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Lake_CliError_toString___closed__1));
x_5 = lean_string_append(x_4, x_3);
lean_dec_ref(x_3);
x_6 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = ((lean_object*)(l_Lake_CliError_toString___closed__3));
x_10 = lean_string_append(x_9, x_8);
lean_dec_ref(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = ((lean_object*)(l_Lake_CliError_toString___closed__3));
x_14 = lean_string_append(x_13, x_12);
lean_dec_ref(x_12);
x_15 = ((lean_object*)(l_Lake_CliError_toString___closed__4));
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_11);
lean_dec_ref(x_11);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = ((lean_object*)(l_Lake_CliError_toString___closed__5));
x_21 = lean_string_append(x_20, x_18);
lean_dec_ref(x_18);
x_22 = ((lean_object*)(l_Lake_CliError_toString___closed__6));
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_19);
lean_dec_ref(x_19);
return x_24;
}
case 5:
{
uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_26 = ((lean_object*)(l_Lake_CliError_toString___closed__7));
x_27 = ((lean_object*)(l_Lake_CliError_toString___closed__8));
x_28 = lean_string_push(x_27, x_25);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_31 = lean_string_append(x_29, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lake_CliError_toString___closed__9));
x_34 = lean_string_append(x_33, x_32);
lean_dec_ref(x_32);
x_35 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_36 = lean_string_append(x_34, x_35);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = ((lean_object*)(l_Lake_CliError_toString___closed__10));
x_39 = ((lean_object*)(l_Lake_CliError_toString___closed__11));
x_40 = l_String_intercalate(x_39, x_37);
x_41 = lean_string_append(x_38, x_40);
lean_dec_ref(x_40);
return x_41;
}
case 8:
{
lean_object* x_42; 
x_42 = ((lean_object*)(l_Lake_CliError_toString___closed__12));
return x_42;
}
case 9:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_43);
lean_dec_ref(x_1);
x_44 = ((lean_object*)(l_Lake_CliError_toString___closed__13));
x_45 = lean_string_append(x_44, x_43);
lean_dec_ref(x_43);
x_46 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_47 = lean_string_append(x_45, x_46);
return x_47;
}
case 10:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_49 = ((lean_object*)(l_Lake_CliError_toString___closed__15));
x_50 = lean_string_append(x_49, x_48);
lean_dec_ref(x_48);
x_51 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_52 = lean_string_append(x_50, x_51);
return x_52;
}
case 11:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec_ref(x_1);
x_54 = ((lean_object*)(l_Lake_CliError_toString___closed__16));
x_55 = 0;
x_56 = l_Lean_Name_toString(x_53, x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec_ref(x_56);
x_58 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_59 = lean_string_append(x_57, x_58);
return x_59;
}
case 12:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_1);
x_61 = ((lean_object*)(l_Lake_CliError_toString___closed__17));
x_62 = lean_string_append(x_61, x_60);
lean_dec_ref(x_60);
x_63 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_64 = lean_string_append(x_62, x_63);
return x_64;
}
case 13:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_65);
lean_dec_ref(x_1);
x_66 = ((lean_object*)(l_Lake_CliError_toString___closed__18));
x_67 = lean_string_append(x_66, x_65);
lean_dec_ref(x_65);
x_68 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_69 = lean_string_append(x_67, x_68);
return x_69;
}
case 14:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_dec_ref(x_1);
x_72 = ((lean_object*)(l_Lake_CliError_toString___closed__19));
x_73 = lean_string_append(x_72, x_70);
lean_dec_ref(x_70);
x_74 = ((lean_object*)(l_Lake_CliError_toString___closed__20));
x_75 = lean_string_append(x_73, x_74);
x_76 = 0;
x_77 = l_Lean_Name_toString(x_71, x_76);
x_78 = lean_string_append(x_75, x_77);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_80 = lean_string_append(x_78, x_79);
return x_80;
}
case 15:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec_ref(x_1);
x_82 = ((lean_object*)(l_Lake_CliError_toString___closed__21));
x_83 = 0;
x_84 = l_Lean_Name_toString(x_81, x_83);
x_85 = lean_string_append(x_82, x_84);
lean_dec_ref(x_84);
x_86 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_87 = lean_string_append(x_85, x_86);
return x_87;
}
case 16:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_dec_ref(x_1);
x_90 = ((lean_object*)(l_Lake_CliError_toString___closed__22));
x_91 = 0;
x_92 = l_Lean_Name_toString(x_88, x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_94 = ((lean_object*)(l_Lake_CliError_toString___closed__23));
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Lean_Name_toString(x_89, x_91);
x_97 = lean_string_append(x_95, x_96);
lean_dec_ref(x_96);
x_98 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_99 = lean_string_append(x_97, x_98);
return x_99;
}
case 17:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_101);
lean_dec_ref(x_1);
x_102 = ((lean_object*)(l_Lake_CliError_toString___closed__22));
x_103 = 0;
x_104 = l_Lean_Name_toString(x_100, x_103);
x_105 = lean_string_append(x_102, x_104);
lean_dec_ref(x_104);
x_106 = ((lean_object*)(l_Lake_CliError_toString___closed__24));
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_101);
lean_dec_ref(x_101);
x_109 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_110 = lean_string_append(x_108, x_109);
return x_110;
}
case 18:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_111);
lean_dec_ref(x_1);
x_112 = ((lean_object*)(l_Lake_CliError_toString___closed__2));
x_113 = lean_string_append(x_112, x_111);
lean_dec_ref(x_111);
x_114 = ((lean_object*)(l_Lake_CliError_toString___closed__25));
x_115 = lean_string_append(x_113, x_114);
return x_115;
}
case 19:
{
lean_object* x_116; uint32_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_118 = ((lean_object*)(l_Lake_CliError_toString___closed__26));
x_119 = lean_string_append(x_118, x_116);
lean_dec_ref(x_116);
x_120 = ((lean_object*)(l_Lake_CliError_toString___closed__27));
x_121 = lean_string_append(x_119, x_120);
x_122 = ((lean_object*)(l_Lake_CliError_toString___closed__8));
x_123 = lean_string_push(x_122, x_117);
x_124 = lean_string_append(x_121, x_123);
lean_dec_ref(x_123);
x_125 = ((lean_object*)(l_Lake_CliError_toString___closed__28));
x_126 = lean_string_append(x_124, x_125);
return x_126;
}
case 20:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
lean_dec_ref(x_1);
x_129 = ((lean_object*)(l_Lake_CliError_toString___closed__29));
x_130 = 0;
x_131 = l_Lean_Name_toString(x_128, x_130);
x_132 = lean_string_append(x_129, x_131);
lean_dec_ref(x_131);
x_133 = ((lean_object*)(l_Lake_CliError_toString___closed__30));
x_134 = lean_string_append(x_132, x_133);
x_135 = l_Lean_Name_toString(x_127, x_130);
x_136 = lean_string_append(x_134, x_135);
lean_dec_ref(x_135);
x_137 = ((lean_object*)(l_Lake_CliError_toString___closed__31));
x_138 = lean_string_append(x_136, x_137);
return x_138;
}
case 21:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_139);
lean_dec_ref(x_1);
x_140 = ((lean_object*)(l_Lake_CliError_toString___closed__32));
x_141 = lean_string_append(x_140, x_139);
lean_dec_ref(x_139);
return x_141;
}
case 22:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_142);
lean_dec_ref(x_1);
x_143 = ((lean_object*)(l_Lake_CliError_toString___closed__33));
x_144 = lean_string_append(x_143, x_142);
lean_dec_ref(x_142);
return x_144;
}
case 23:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_145);
lean_dec_ref(x_1);
x_146 = ((lean_object*)(l_Lake_CliError_toString___closed__34));
x_147 = lean_string_append(x_146, x_145);
lean_dec_ref(x_145);
x_148 = ((lean_object*)(l_Lake_CliError_toString___closed__14));
x_149 = lean_string_append(x_147, x_148);
return x_149;
}
case 24:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_150);
lean_dec_ref(x_1);
x_151 = ((lean_object*)(l_Lake_CliError_toString___closed__35));
x_152 = lean_string_append(x_151, x_150);
lean_dec_ref(x_150);
x_153 = ((lean_object*)(l_Lake_CliError_toString___closed__36));
x_154 = lean_string_append(x_152, x_153);
return x_154;
}
case 25:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_155);
lean_dec_ref(x_1);
x_156 = ((lean_object*)(l_Lake_CliError_toString___closed__37));
x_157 = lean_string_append(x_156, x_155);
lean_dec_ref(x_155);
return x_157;
}
case 26:
{
lean_object* x_158; 
x_158 = ((lean_object*)(l_Lake_CliError_toString___closed__38));
return x_158;
}
case 27:
{
lean_object* x_159; 
x_159 = ((lean_object*)(l_Lake_CliError_toString___closed__39));
return x_159;
}
case 28:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_161);
lean_dec_ref(x_1);
x_162 = ((lean_object*)(l_Lake_CliError_toString___closed__40));
x_163 = lean_string_append(x_162, x_160);
lean_dec_ref(x_160);
x_164 = ((lean_object*)(l_Lake_CliError_toString___closed__41));
x_165 = lean_string_append(x_163, x_164);
x_166 = lean_string_utf8_byte_size(x_161);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_string_append(x_165, x_161);
lean_dec_ref(x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_161);
x_170 = ((lean_object*)(l_Lake_CliError_toString___closed__42));
x_171 = lean_string_append(x_165, x_170);
return x_171;
}
}
case 29:
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_172);
lean_dec_ref(x_1);
return x_172;
}
default: 
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_173);
lean_dec_ref(x_1);
x_174 = ((lean_object*)(l_Lake_CliError_toString___closed__43));
x_175 = lean_string_append(x_174, x_173);
lean_dec_ref(x_173);
return x_175;
}
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCliError_default = _init_l_Lake_instInhabitedCliError_default();
lean_mark_persistent(l_Lake_instInhabitedCliError_default);
l_Lake_instInhabitedCliError = _init_l_Lake_instInhabitedCliError();
lean_mark_persistent(l_Lake_instInhabitedCliError);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Error(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Error(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Error(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Error(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Error(builtin);
}
#ifdef __cplusplus
}
#endif

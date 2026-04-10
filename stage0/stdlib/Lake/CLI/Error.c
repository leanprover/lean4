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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static lean_once_cell_t l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value;
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
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object*);
static const lean_closure_object l_Lake_CliError_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CliError_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CliError_instToString___closed__0 = (const lean_object*)&l_Lake_CliError_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CliError_instToString = (const lean_object*)&l_Lake_CliError_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
case 9:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
case 10:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(10u);
return v___x_12_;
}
case 11:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(11u);
return v___x_13_;
}
case 12:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(12u);
return v___x_14_;
}
case 13:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(13u);
return v___x_15_;
}
case 14:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(14u);
return v___x_16_;
}
case 15:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(15u);
return v___x_17_;
}
case 16:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(16u);
return v___x_18_;
}
case 17:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(17u);
return v___x_19_;
}
case 18:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(18u);
return v___x_20_;
}
case 19:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(19u);
return v___x_21_;
}
case 20:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(20u);
return v___x_22_;
}
case 21:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(21u);
return v___x_23_;
}
case 22:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(22u);
return v___x_24_;
}
case 23:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(23u);
return v___x_25_;
}
case 24:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(24u);
return v___x_26_;
}
case 25:
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(25u);
return v___x_27_;
}
case 26:
{
lean_object* v___x_28_; 
v___x_28_ = lean_unsigned_to_nat(26u);
return v___x_28_;
}
case 27:
{
lean_object* v___x_29_; 
v___x_29_ = lean_unsigned_to_nat(27u);
return v___x_29_;
}
case 28:
{
lean_object* v___x_30_; 
v___x_30_ = lean_unsigned_to_nat(28u);
return v___x_30_;
}
case 29:
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(29u);
return v___x_31_;
}
default: 
{
lean_object* v___x_32_; 
v___x_32_ = lean_unsigned_to_nat(30u);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___boxed(lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_CliError_ctorIdx(v_x_33_);
lean_dec(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___redArg(lean_object* v_t_35_, lean_object* v_k_36_){
_start:
{
switch(lean_obj_tag(v_t_35_))
{
case 1:
{
lean_object* v_cmd_37_; lean_object* v___x_38_; 
v_cmd_37_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_cmd_37_);
lean_dec_ref(v_t_35_);
v___x_38_ = lean_apply_1(v_k_36_, v_cmd_37_);
return v___x_38_;
}
case 2:
{
lean_object* v_arg_39_; lean_object* v___x_40_; 
v_arg_39_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_arg_39_);
lean_dec_ref(v_t_35_);
v___x_40_ = lean_apply_1(v_k_36_, v_arg_39_);
return v___x_40_;
}
case 3:
{
lean_object* v_opt_41_; lean_object* v_arg_42_; lean_object* v___x_43_; 
v_opt_41_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_opt_41_);
v_arg_42_ = lean_ctor_get(v_t_35_, 1);
lean_inc_ref(v_arg_42_);
lean_dec_ref(v_t_35_);
v___x_43_ = lean_apply_2(v_k_36_, v_opt_41_, v_arg_42_);
return v___x_43_;
}
case 4:
{
lean_object* v_opt_44_; lean_object* v_arg_45_; lean_object* v___x_46_; 
v_opt_44_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_opt_44_);
v_arg_45_ = lean_ctor_get(v_t_35_, 1);
lean_inc_ref(v_arg_45_);
lean_dec_ref(v_t_35_);
v___x_46_ = lean_apply_2(v_k_36_, v_opt_44_, v_arg_45_);
return v___x_46_;
}
case 5:
{
uint32_t v_opt_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_opt_47_ = lean_ctor_get_uint32(v_t_35_, 0);
lean_dec_ref(v_t_35_);
v___x_48_ = lean_box_uint32(v_opt_47_);
v___x_49_ = lean_apply_1(v_k_36_, v___x_48_);
return v___x_49_;
}
case 6:
{
lean_object* v_opt_50_; lean_object* v___x_51_; 
v_opt_50_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_opt_50_);
lean_dec_ref(v_t_35_);
v___x_51_ = lean_apply_1(v_k_36_, v_opt_50_);
return v___x_51_;
}
case 7:
{
lean_object* v_args_52_; lean_object* v___x_53_; 
v_args_52_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_args_52_);
lean_dec_ref(v_t_35_);
v___x_53_ = lean_apply_1(v_k_36_, v_args_52_);
return v___x_53_;
}
case 9:
{
lean_object* v_spec_54_; lean_object* v___x_55_; 
v_spec_54_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_54_);
lean_dec_ref(v_t_35_);
v___x_55_ = lean_apply_1(v_k_36_, v_spec_54_);
return v___x_55_;
}
case 10:
{
lean_object* v_spec_56_; lean_object* v___x_57_; 
v_spec_56_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_56_);
lean_dec_ref(v_t_35_);
v___x_57_ = lean_apply_1(v_k_36_, v_spec_56_);
return v___x_57_;
}
case 11:
{
lean_object* v_mod_58_; lean_object* v___x_59_; 
v_mod_58_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_mod_58_);
lean_dec_ref(v_t_35_);
v___x_59_ = lean_apply_1(v_k_36_, v_mod_58_);
return v___x_59_;
}
case 12:
{
lean_object* v_path_60_; lean_object* v___x_61_; 
v_path_60_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_path_60_);
lean_dec_ref(v_t_35_);
v___x_61_ = lean_apply_1(v_k_36_, v_path_60_);
return v___x_61_;
}
case 13:
{
lean_object* v_spec_62_; lean_object* v___x_63_; 
v_spec_62_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_62_);
lean_dec_ref(v_t_35_);
v___x_63_ = lean_apply_1(v_k_36_, v_spec_62_);
return v___x_63_;
}
case 14:
{
lean_object* v_type_64_; lean_object* v_facet_65_; lean_object* v___x_66_; 
v_type_64_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_type_64_);
v_facet_65_ = lean_ctor_get(v_t_35_, 1);
lean_inc(v_facet_65_);
lean_dec_ref(v_t_35_);
v___x_66_ = lean_apply_2(v_k_36_, v_type_64_, v_facet_65_);
return v___x_66_;
}
case 15:
{
lean_object* v_target_67_; lean_object* v___x_68_; 
v_target_67_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_target_67_);
lean_dec_ref(v_t_35_);
v___x_68_ = lean_apply_1(v_k_36_, v_target_67_);
return v___x_68_;
}
case 16:
{
lean_object* v_pkg_69_; lean_object* v_mod_70_; lean_object* v___x_71_; 
v_pkg_69_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_pkg_69_);
v_mod_70_ = lean_ctor_get(v_t_35_, 1);
lean_inc(v_mod_70_);
lean_dec_ref(v_t_35_);
v___x_71_ = lean_apply_2(v_k_36_, v_pkg_69_, v_mod_70_);
return v___x_71_;
}
case 17:
{
lean_object* v_pkg_72_; lean_object* v_spec_73_; lean_object* v___x_74_; 
v_pkg_72_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_pkg_72_);
v_spec_73_ = lean_ctor_get(v_t_35_, 1);
lean_inc_ref(v_spec_73_);
lean_dec_ref(v_t_35_);
v___x_74_ = lean_apply_2(v_k_36_, v_pkg_72_, v_spec_73_);
return v___x_74_;
}
case 18:
{
lean_object* v_key_75_; lean_object* v___x_76_; 
v_key_75_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_key_75_);
lean_dec_ref(v_t_35_);
v___x_76_ = lean_apply_1(v_k_36_, v_key_75_);
return v___x_76_;
}
case 19:
{
lean_object* v_spec_77_; uint32_t v_tooMany_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_spec_77_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_77_);
v_tooMany_78_ = lean_ctor_get_uint32(v_t_35_, sizeof(void*)*1);
lean_dec_ref(v_t_35_);
v___x_79_ = lean_box_uint32(v_tooMany_78_);
v___x_80_ = lean_apply_2(v_k_36_, v_spec_77_, v___x_79_);
return v___x_80_;
}
case 20:
{
lean_object* v_target_81_; lean_object* v_facet_82_; lean_object* v___x_83_; 
v_target_81_ = lean_ctor_get(v_t_35_, 0);
lean_inc(v_target_81_);
v_facet_82_ = lean_ctor_get(v_t_35_, 1);
lean_inc(v_facet_82_);
lean_dec_ref(v_t_35_);
v___x_83_ = lean_apply_2(v_k_36_, v_target_81_, v_facet_82_);
return v___x_83_;
}
case 21:
{
lean_object* v_spec_84_; lean_object* v___x_85_; 
v_spec_84_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_84_);
lean_dec_ref(v_t_35_);
v___x_85_ = lean_apply_1(v_k_36_, v_spec_84_);
return v___x_85_;
}
case 22:
{
lean_object* v_script_86_; lean_object* v___x_87_; 
v_script_86_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_script_86_);
lean_dec_ref(v_t_35_);
v___x_87_ = lean_apply_1(v_k_36_, v_script_86_);
return v___x_87_;
}
case 23:
{
lean_object* v_script_88_; lean_object* v___x_89_; 
v_script_88_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_script_88_);
lean_dec_ref(v_t_35_);
v___x_89_ = lean_apply_1(v_k_36_, v_script_88_);
return v___x_89_;
}
case 24:
{
lean_object* v_spec_90_; lean_object* v___x_91_; 
v_spec_90_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_spec_90_);
lean_dec_ref(v_t_35_);
v___x_91_ = lean_apply_1(v_k_36_, v_spec_90_);
return v___x_91_;
}
case 25:
{
lean_object* v_path_92_; lean_object* v___x_93_; 
v_path_92_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_path_92_);
lean_dec_ref(v_t_35_);
v___x_93_ = lean_apply_1(v_k_36_, v_path_92_);
return v___x_93_;
}
case 28:
{
lean_object* v_expected_94_; lean_object* v_actual_95_; lean_object* v___x_96_; 
v_expected_94_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_expected_94_);
v_actual_95_ = lean_ctor_get(v_t_35_, 1);
lean_inc_ref(v_actual_95_);
lean_dec_ref(v_t_35_);
v___x_96_ = lean_apply_2(v_k_36_, v_expected_94_, v_actual_95_);
return v___x_96_;
}
case 29:
{
lean_object* v_msg_97_; lean_object* v___x_98_; 
v_msg_97_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_msg_97_);
lean_dec_ref(v_t_35_);
v___x_98_ = lean_apply_1(v_k_36_, v_msg_97_);
return v___x_98_;
}
case 30:
{
lean_object* v_path_99_; lean_object* v___x_100_; 
v_path_99_ = lean_ctor_get(v_t_35_, 0);
lean_inc_ref(v_path_99_);
lean_dec_ref(v_t_35_);
v___x_100_ = lean_apply_1(v_k_36_, v_path_99_);
return v___x_100_;
}
default: 
{
lean_dec(v_t_35_);
return v_k_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim(lean_object* v_motive_101_, lean_object* v_ctorIdx_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lake_CliError_ctorElim___redArg(v_t_103_, v_k_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___boxed(lean_object* v_motive_107_, lean_object* v_ctorIdx_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_k_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lake_CliError_ctorElim(v_motive_107_, v_ctorIdx_108_, v_t_109_, v_h_110_, v_k_111_);
lean_dec(v_ctorIdx_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim___redArg(lean_object* v_t_113_, lean_object* v_missingCommand_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lake_CliError_ctorElim___redArg(v_t_113_, v_missingCommand_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_missingCommand_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lake_CliError_ctorElim___redArg(v_t_117_, v_missingCommand_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim___redArg(lean_object* v_t_121_, lean_object* v_unknownCommand_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lake_CliError_ctorElim___redArg(v_t_121_, v_unknownCommand_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_unknownCommand_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lake_CliError_ctorElim___redArg(v_t_125_, v_unknownCommand_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim___redArg(lean_object* v_t_129_, lean_object* v_missingArg_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lake_CliError_ctorElim___redArg(v_t_129_, v_missingArg_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_missingArg_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lake_CliError_ctorElim___redArg(v_t_133_, v_missingArg_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim___redArg(lean_object* v_t_137_, lean_object* v_missingOptArg_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lake_CliError_ctorElim___redArg(v_t_137_, v_missingOptArg_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_missingOptArg_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lake_CliError_ctorElim___redArg(v_t_141_, v_missingOptArg_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim___redArg(lean_object* v_t_145_, lean_object* v_invalidOptArg_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lake_CliError_ctorElim___redArg(v_t_145_, v_invalidOptArg_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim(lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_invalidOptArg_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lake_CliError_ctorElim___redArg(v_t_149_, v_invalidOptArg_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim___redArg(lean_object* v_t_153_, lean_object* v_unknownShortOption_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lake_CliError_ctorElim___redArg(v_t_153_, v_unknownShortOption_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim(lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_unknownShortOption_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lake_CliError_ctorElim___redArg(v_t_157_, v_unknownShortOption_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim___redArg(lean_object* v_t_161_, lean_object* v_unknownLongOption_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lake_CliError_ctorElim___redArg(v_t_161_, v_unknownLongOption_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_unknownLongOption_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lake_CliError_ctorElim___redArg(v_t_165_, v_unknownLongOption_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim___redArg(lean_object* v_t_169_, lean_object* v_unexpectedArguments_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lake_CliError_ctorElim___redArg(v_t_169_, v_unexpectedArguments_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_unexpectedArguments_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lake_CliError_ctorElim___redArg(v_t_173_, v_unexpectedArguments_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim___redArg(lean_object* v_t_177_, lean_object* v_unexpectedPlus_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lake_CliError_ctorElim___redArg(v_t_177_, v_unexpectedPlus_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_unexpectedPlus_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lake_CliError_ctorElim___redArg(v_t_181_, v_unexpectedPlus_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim___redArg(lean_object* v_t_185_, lean_object* v_unknownTemplate_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lake_CliError_ctorElim___redArg(v_t_185_, v_unknownTemplate_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_unknownTemplate_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lake_CliError_ctorElim___redArg(v_t_189_, v_unknownTemplate_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim___redArg(lean_object* v_t_193_, lean_object* v_unknownConfigLang_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lake_CliError_ctorElim___redArg(v_t_193_, v_unknownConfigLang_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_unknownConfigLang_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lake_CliError_ctorElim___redArg(v_t_197_, v_unknownConfigLang_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim___redArg(lean_object* v_t_201_, lean_object* v_unknownModule_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lake_CliError_ctorElim___redArg(v_t_201_, v_unknownModule_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_unknownModule_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lake_CliError_ctorElim___redArg(v_t_205_, v_unknownModule_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim___redArg(lean_object* v_t_209_, lean_object* v_unknownModulePath_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lake_CliError_ctorElim___redArg(v_t_209_, v_unknownModulePath_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_unknownModulePath_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lake_CliError_ctorElim___redArg(v_t_213_, v_unknownModulePath_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim___redArg(lean_object* v_t_217_, lean_object* v_unknownPackage_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lake_CliError_ctorElim___redArg(v_t_217_, v_unknownPackage_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim(lean_object* v_motive_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_unknownPackage_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lake_CliError_ctorElim___redArg(v_t_221_, v_unknownPackage_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim___redArg(lean_object* v_t_225_, lean_object* v_unknownFacet_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lake_CliError_ctorElim___redArg(v_t_225_, v_unknownFacet_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_unknownFacet_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lake_CliError_ctorElim___redArg(v_t_229_, v_unknownFacet_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim___redArg(lean_object* v_t_233_, lean_object* v_unknownTarget_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lake_CliError_ctorElim___redArg(v_t_233_, v_unknownTarget_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_unknownTarget_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lake_CliError_ctorElim___redArg(v_t_237_, v_unknownTarget_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim___redArg(lean_object* v_t_241_, lean_object* v_missingModule_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lake_CliError_ctorElim___redArg(v_t_241_, v_missingModule_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim(lean_object* v_motive_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_missingModule_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lake_CliError_ctorElim___redArg(v_t_245_, v_missingModule_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim___redArg(lean_object* v_t_249_, lean_object* v_missingTarget_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lake_CliError_ctorElim___redArg(v_t_249_, v_missingTarget_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_missingTarget_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lake_CliError_ctorElim___redArg(v_t_253_, v_missingTarget_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim___redArg(lean_object* v_t_257_, lean_object* v_invalidBuildTarget_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lake_CliError_ctorElim___redArg(v_t_257_, v_invalidBuildTarget_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim(lean_object* v_motive_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_invalidBuildTarget_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lake_CliError_ctorElim___redArg(v_t_261_, v_invalidBuildTarget_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim___redArg(lean_object* v_t_265_, lean_object* v_invalidTargetSpec_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lake_CliError_ctorElim___redArg(v_t_265_, v_invalidTargetSpec_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim(lean_object* v_motive_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_invalidTargetSpec_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lake_CliError_ctorElim___redArg(v_t_269_, v_invalidTargetSpec_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim___redArg(lean_object* v_t_273_, lean_object* v_invalidFacet_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lake_CliError_ctorElim___redArg(v_t_273_, v_invalidFacet_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_invalidFacet_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lake_CliError_ctorElim___redArg(v_t_277_, v_invalidFacet_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim___redArg(lean_object* v_t_281_, lean_object* v_unknownExe_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lake_CliError_ctorElim___redArg(v_t_281_, v_unknownExe_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_unknownExe_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lake_CliError_ctorElim___redArg(v_t_285_, v_unknownExe_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim___redArg(lean_object* v_t_289_, lean_object* v_unknownScript_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lake_CliError_ctorElim___redArg(v_t_289_, v_unknownScript_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_unknownScript_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lake_CliError_ctorElim___redArg(v_t_293_, v_unknownScript_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim___redArg(lean_object* v_t_297_, lean_object* v_missingScriptDoc_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lake_CliError_ctorElim___redArg(v_t_297_, v_missingScriptDoc_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_missingScriptDoc_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lake_CliError_ctorElim___redArg(v_t_301_, v_missingScriptDoc_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim___redArg(lean_object* v_t_305_, lean_object* v_invalidScriptSpec_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lake_CliError_ctorElim___redArg(v_t_305_, v_invalidScriptSpec_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim(lean_object* v_motive_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_invalidScriptSpec_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lake_CliError_ctorElim___redArg(v_t_309_, v_invalidScriptSpec_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim___redArg(lean_object* v_t_313_, lean_object* v_outputConfigExists_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lake_CliError_ctorElim___redArg(v_t_313_, v_outputConfigExists_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_outputConfigExists_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lake_CliError_ctorElim___redArg(v_t_317_, v_outputConfigExists_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim___redArg(lean_object* v_t_321_, lean_object* v_unknownLeanInstall_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lake_CliError_ctorElim___redArg(v_t_321_, v_unknownLeanInstall_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim(lean_object* v_motive_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_unknownLeanInstall_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lake_CliError_ctorElim___redArg(v_t_325_, v_unknownLeanInstall_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim___redArg(lean_object* v_t_329_, lean_object* v_unknownLakeInstall_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lake_CliError_ctorElim___redArg(v_t_329_, v_unknownLakeInstall_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_unknownLakeInstall_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lake_CliError_ctorElim___redArg(v_t_333_, v_unknownLakeInstall_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim___redArg(lean_object* v_t_337_, lean_object* v_leanRevMismatch_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lake_CliError_ctorElim___redArg(v_t_337_, v_leanRevMismatch_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_leanRevMismatch_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lake_CliError_ctorElim___redArg(v_t_341_, v_leanRevMismatch_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim___redArg(lean_object* v_t_345_, lean_object* v_invalidEnv_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lake_CliError_ctorElim___redArg(v_t_345_, v_invalidEnv_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim(lean_object* v_motive_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_invalidEnv_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lake_CliError_ctorElim___redArg(v_t_349_, v_invalidEnv_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim___redArg(lean_object* v_t_353_, lean_object* v_missingRootDir_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lake_CliError_ctorElim___redArg(v_t_353_, v_missingRootDir_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim(lean_object* v_motive_356_, lean_object* v_t_357_, lean_object* v_h_358_, lean_object* v_missingRootDir_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lake_CliError_ctorElim___redArg(v_t_357_, v_missingRootDir_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError_default(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(lean_object* v___y_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_String_quote(v___y_363_);
v___x_365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_dec(v_x_366_);
return v_x_367_;
}
else
{
lean_object* v_head_369_; lean_object* v_tail_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_381_; 
v_head_369_ = lean_ctor_get(v_x_368_, 0);
v_tail_370_ = lean_ctor_get(v_x_368_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_372_ = v_x_368_;
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_tail_370_);
lean_inc(v_head_369_);
lean_dec(v_x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
lean_inc(v_x_366_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 5);
lean_ctor_set(v___x_372_, 1, v_x_366_);
lean_ctor_set(v___x_372_, 0, v_x_367_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_x_367_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_x_366_);
v___x_375_ = v_reuseFailAlloc_380_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = l_String_quote(v_head_369_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_375_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v_x_367_ = v___x_378_;
v_x_368_ = v_tail_370_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_dec(v_x_382_);
return v_x_383_;
}
else
{
lean_object* v_head_385_; lean_object* v_tail_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v_head_385_ = lean_ctor_get(v_x_384_, 0);
v_tail_386_ = lean_ctor_get(v_x_384_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_388_ = v_x_384_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_tail_386_);
lean_inc(v_head_385_);
lean_dec(v_x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
lean_inc(v_x_382_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 5);
lean_ctor_set(v___x_388_, 1, v_x_382_);
lean_ctor_set(v___x_388_, 0, v_x_383_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_x_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_x_382_);
v___x_391_ = v_reuseFailAlloc_396_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = l_String_quote(v_head_385_);
v___x_393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(v_x_382_, v___x_394_, v_tail_386_);
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_400_; 
lean_dec(v_x_399_);
v___x_400_ = lean_box(0);
return v___x_400_;
}
else
{
lean_object* v_tail_401_; 
v_tail_401_ = lean_ctor_get(v_x_398_, 1);
if (lean_obj_tag(v_tail_401_) == 0)
{
lean_object* v_head_402_; lean_object* v___x_403_; 
lean_dec(v_x_399_);
v_head_402_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_head_402_);
lean_dec_ref(v_x_398_);
v___x_403_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_402_);
return v___x_403_;
}
else
{
lean_object* v_head_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_tail_401_);
v_head_404_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_head_404_);
lean_dec_ref(v_x_398_);
v___x_405_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_404_);
v___x_406_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(v_x_399_, v___x_405_, v_tail_401_);
return v___x_406_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2));
v___x_419_ = lean_string_length(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7);
v___x_421_ = lean_nat_to_int(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(lean_object* v_a_426_){
_start:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1));
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_428_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5));
v___x_429_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(v_a_426_, v___x_428_);
v___x_430_ = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8);
v___x_431_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9));
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_429_);
v___x_433_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10));
v___x_434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_430_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = l_Std_Format_fill(v___x_435_);
return v___x_436_;
}
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__8(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(2u);
v___x_450_ = lean_nat_to_int(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__9(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_to_int(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr(lean_object* v_x_618_, lean_object* v_prec_619_){
_start:
{
lean_object* v___y_621_; lean_object* v___y_628_; lean_object* v___y_635_; lean_object* v___y_642_; 
switch(lean_obj_tag(v_x_618_))
{
case 0:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(1024u);
v___x_649_ = lean_nat_dec_le(v___x_648_, v_prec_619_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_635_ = v___x_650_;
goto v___jp_634_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_635_ = v___x_651_;
goto v___jp_634_;
}
}
case 1:
{
lean_object* v_cmd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_672_; 
v_cmd_652_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_672_ == 0)
{
v___x_654_ = v_x_618_;
v_isShared_655_ = v_isSharedCheck_672_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_cmd_652_);
lean_dec(v_x_618_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_672_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___y_657_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(1024u);
v___x_669_ = lean_nat_dec_le(v___x_668_, v_prec_619_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_657_ = v___x_670_;
goto v___jp_656_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_657_ = v___x_671_;
goto v___jp_656_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__12));
v___x_659_ = l_String_quote(v_cmd_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 3);
lean_ctor_set(v___x_654_, 0, v___x_659_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_667_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_658_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
lean_inc(v___y_657_);
v___x_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_657_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = 0;
v___x_665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*1, v___x_664_);
v___x_666_ = l_Repr_addAppParen(v___x_665_, v_prec_619_);
return v___x_666_;
}
}
}
}
case 2:
{
lean_object* v_arg_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_693_; 
v_arg_673_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_693_ == 0)
{
v___x_675_ = v_x_618_;
v_isShared_676_ = v_isSharedCheck_693_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_arg_673_);
lean_dec(v_x_618_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_693_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___y_678_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1024u);
v___x_690_ = lean_nat_dec_le(v___x_689_, v_prec_619_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_678_ = v___x_691_;
goto v___jp_677_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_678_ = v___x_692_;
goto v___jp_677_;
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__15));
v___x_680_ = l_String_quote(v_arg_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 3);
lean_ctor_set(v___x_675_, 0, v___x_680_);
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_688_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_679_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_inc(v___y_678_);
v___x_684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_678_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = 0;
v___x_686_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*1, v___x_685_);
v___x_687_ = l_Repr_addAppParen(v___x_686_, v_prec_619_);
return v___x_687_;
}
}
}
}
case 3:
{
lean_object* v_opt_694_; lean_object* v_arg_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_720_; 
v_opt_694_ = lean_ctor_get(v_x_618_, 0);
v_arg_695_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_720_ == 0)
{
v___x_697_ = v_x_618_;
v_isShared_698_ = v_isSharedCheck_720_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_arg_695_);
lean_inc(v_opt_694_);
lean_dec(v_x_618_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_720_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___y_700_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(1024u);
v___x_717_ = lean_nat_dec_le(v___x_716_, v_prec_619_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_700_ = v___x_718_;
goto v___jp_699_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_700_ = v___x_719_;
goto v___jp_699_;
}
v___jp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_701_ = lean_box(1);
v___x_702_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__18));
v___x_703_ = l_String_quote(v_opt_694_);
v___x_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 5);
lean_ctor_set(v___x_697_, 1, v___x_704_);
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_706_ = v___x_697_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_715_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_701_);
v___x_708_ = l_String_quote(v_arg_695_);
v___x_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_707_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
lean_inc(v___y_700_);
v___x_711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_711_, 0, v___y_700_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = 0;
v___x_713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set_uint8(v___x_713_, sizeof(void*)*1, v___x_712_);
v___x_714_ = l_Repr_addAppParen(v___x_713_, v_prec_619_);
return v___x_714_;
}
}
}
}
case 4:
{
lean_object* v_opt_721_; lean_object* v_arg_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_747_; 
v_opt_721_ = lean_ctor_get(v_x_618_, 0);
v_arg_722_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_747_ == 0)
{
v___x_724_ = v_x_618_;
v_isShared_725_ = v_isSharedCheck_747_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_arg_722_);
lean_inc(v_opt_721_);
lean_dec(v_x_618_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_747_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___y_727_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1024u);
v___x_744_ = lean_nat_dec_le(v___x_743_, v_prec_619_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
v___x_745_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_727_ = v___x_745_;
goto v___jp_726_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_727_ = v___x_746_;
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_728_ = lean_box(1);
v___x_729_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__21));
v___x_730_ = l_String_quote(v_opt_721_);
v___x_731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 5);
lean_ctor_set(v___x_724_, 1, v___x_731_);
lean_ctor_set(v___x_724_, 0, v___x_729_);
v___x_733_ = v___x_724_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_742_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_728_);
v___x_735_ = l_String_quote(v_arg_722_);
v___x_736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_734_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
lean_inc(v___y_727_);
v___x_738_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_738_, 0, v___y_727_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = 0;
v___x_740_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_739_);
v___x_741_ = l_Repr_addAppParen(v___x_740_, v_prec_619_);
return v___x_741_;
}
}
}
}
case 5:
{
uint32_t v_opt_748_; lean_object* v___y_750_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_opt_748_ = lean_ctor_get_uint32(v_x_618_, 0);
lean_dec_ref(v_x_618_);
v___x_759_ = lean_unsigned_to_nat(1024u);
v___x_760_ = lean_nat_dec_le(v___x_759_, v_prec_619_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_750_ = v___x_761_;
goto v___jp_749_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_750_ = v___x_762_;
goto v___jp_749_;
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_751_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__24));
v___x_752_ = l_Char_quote(v_opt_748_);
v___x_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
lean_inc(v___y_750_);
v___x_755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_755_, 0, v___y_750_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = 0;
v___x_757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*1, v___x_756_);
v___x_758_ = l_Repr_addAppParen(v___x_757_, v_prec_619_);
return v___x_758_;
}
}
case 6:
{
lean_object* v_opt_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_783_; 
v_opt_763_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_783_ == 0)
{
v___x_765_ = v_x_618_;
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_opt_763_);
lean_dec(v_x_618_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___y_768_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1024u);
v___x_780_ = lean_nat_dec_le(v___x_779_, v_prec_619_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
v___x_781_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_768_ = v___x_781_;
goto v___jp_767_;
}
else
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_768_ = v___x_782_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__27));
v___x_770_ = l_String_quote(v_opt_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 3);
lean_ctor_set(v___x_765_, 0, v___x_770_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_778_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_769_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_inc(v___y_768_);
v___x_774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_768_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = 0;
v___x_776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*1, v___x_775_);
v___x_777_ = l_Repr_addAppParen(v___x_776_, v_prec_619_);
return v___x_777_;
}
}
}
}
case 7:
{
lean_object* v_args_784_; lean_object* v___y_786_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_args_784_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_args_784_);
lean_dec_ref(v_x_618_);
v___x_794_ = lean_unsigned_to_nat(1024u);
v___x_795_ = lean_nat_dec_le(v___x_794_, v_prec_619_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_786_ = v___x_796_;
goto v___jp_785_;
}
else
{
lean_object* v___x_797_; 
v___x_797_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_786_ = v___x_797_;
goto v___jp_785_;
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_787_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__30));
v___x_788_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(v_args_784_);
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
lean_inc(v___y_786_);
v___x_790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_790_, 0, v___y_786_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = 0;
v___x_792_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*1, v___x_791_);
v___x_793_ = l_Repr_addAppParen(v___x_792_, v_prec_619_);
return v___x_793_;
}
}
case 8:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1024u);
v___x_799_ = lean_nat_dec_le(v___x_798_, v_prec_619_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_642_ = v___x_800_;
goto v___jp_641_;
}
else
{
lean_object* v___x_801_; 
v___x_801_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_642_ = v___x_801_;
goto v___jp_641_;
}
}
case 9:
{
lean_object* v_spec_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_822_; 
v_spec_802_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_822_ == 0)
{
v___x_804_ = v_x_618_;
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_spec_802_);
lean_dec(v_x_618_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_822_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___y_807_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1024u);
v___x_819_ = lean_nat_dec_le(v___x_818_, v_prec_619_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_807_ = v___x_820_;
goto v___jp_806_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_807_ = v___x_821_;
goto v___jp_806_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__33));
v___x_809_ = l_String_quote(v_spec_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 3);
lean_ctor_set(v___x_804_, 0, v___x_809_);
v___x_811_ = v___x_804_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_817_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_808_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
lean_inc(v___y_807_);
v___x_813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_813_, 0, v___y_807_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = 0;
v___x_815_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*1, v___x_814_);
v___x_816_ = l_Repr_addAppParen(v___x_815_, v_prec_619_);
return v___x_816_;
}
}
}
}
case 10:
{
lean_object* v_spec_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_843_; 
v_spec_823_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_843_ == 0)
{
v___x_825_ = v_x_618_;
v_isShared_826_ = v_isSharedCheck_843_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_spec_823_);
lean_dec(v_x_618_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_843_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___y_828_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_unsigned_to_nat(1024u);
v___x_840_ = lean_nat_dec_le(v___x_839_, v_prec_619_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_828_ = v___x_841_;
goto v___jp_827_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_828_ = v___x_842_;
goto v___jp_827_;
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_829_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__36));
v___x_830_ = l_String_quote(v_spec_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 3);
lean_ctor_set(v___x_825_, 0, v___x_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_838_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_829_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_inc(v___y_828_);
v___x_834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_834_, 0, v___y_828_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = 0;
v___x_836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*1, v___x_835_);
v___x_837_ = l_Repr_addAppParen(v___x_836_, v_prec_619_);
return v___x_837_;
}
}
}
}
case 11:
{
lean_object* v_mod_844_; lean_object* v___y_846_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_mod_844_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_mod_844_);
lean_dec_ref(v_x_618_);
v___x_855_ = lean_unsigned_to_nat(1024u);
v___x_856_ = lean_nat_dec_le(v___x_855_, v_prec_619_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_846_ = v___x_857_;
goto v___jp_845_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_846_ = v___x_858_;
goto v___jp_845_;
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_847_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__39));
v___x_848_ = lean_unsigned_to_nat(1024u);
v___x_849_ = l_Lean_Name_reprPrec(v_mod_844_, v___x_848_);
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_847_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
lean_inc(v___y_846_);
v___x_851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_846_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = 0;
v___x_853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*1, v___x_852_);
v___x_854_ = l_Repr_addAppParen(v___x_853_, v_prec_619_);
return v___x_854_;
}
}
case 12:
{
lean_object* v_path_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_883_; 
v_path_859_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_883_ == 0)
{
v___x_861_ = v_x_618_;
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_path_859_);
lean_dec(v_x_618_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___y_864_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1024u);
v___x_880_ = lean_nat_dec_le(v___x_879_, v_prec_619_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_864_ = v___x_881_;
goto v___jp_863_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_864_ = v___x_882_;
goto v___jp_863_;
}
v___jp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_865_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__42));
v___x_866_ = lean_unsigned_to_nat(1024u);
v___x_867_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_868_ = l_String_quote(v_path_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 3);
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_878_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Repr_addAppParen(v___x_871_, v___x_866_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_865_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
lean_inc(v___y_864_);
v___x_874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_864_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v_prec_619_);
return v___x_877_;
}
}
}
}
case 13:
{
lean_object* v_spec_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_904_; 
v_spec_884_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_904_ == 0)
{
v___x_886_ = v_x_618_;
v_isShared_887_ = v_isSharedCheck_904_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_spec_884_);
lean_dec(v_x_618_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_904_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___y_889_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(1024u);
v___x_901_ = lean_nat_dec_le(v___x_900_, v_prec_619_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_889_ = v___x_902_;
goto v___jp_888_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_889_ = v___x_903_;
goto v___jp_888_;
}
v___jp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__47));
v___x_891_ = l_String_quote(v_spec_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 3);
lean_ctor_set(v___x_886_, 0, v___x_891_);
v___x_893_ = v___x_886_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_899_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_890_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
lean_inc(v___y_889_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___y_889_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
v___x_898_ = l_Repr_addAppParen(v___x_897_, v_prec_619_);
return v___x_898_;
}
}
}
}
case 14:
{
lean_object* v_type_905_; lean_object* v_facet_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_931_; 
v_type_905_ = lean_ctor_get(v_x_618_, 0);
v_facet_906_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_931_ == 0)
{
v___x_908_ = v_x_618_;
v_isShared_909_ = v_isSharedCheck_931_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_facet_906_);
lean_inc(v_type_905_);
lean_dec(v_x_618_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_931_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___y_911_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1024u);
v___x_928_ = lean_nat_dec_le(v___x_927_, v_prec_619_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_911_ = v___x_929_;
goto v___jp_910_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_911_ = v___x_930_;
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_912_ = lean_box(1);
v___x_913_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__50));
v___x_914_ = l_String_quote(v_type_905_);
v___x_915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 5);
lean_ctor_set(v___x_908_, 1, v___x_915_);
lean_ctor_set(v___x_908_, 0, v___x_913_);
v___x_917_ = v___x_908_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_926_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_912_);
v___x_919_ = lean_unsigned_to_nat(1024u);
v___x_920_ = l_Lean_Name_reprPrec(v_facet_906_, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_918_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_inc(v___y_911_);
v___x_922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_922_, 0, v___y_911_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = 0;
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_923_);
v___x_925_ = l_Repr_addAppParen(v___x_924_, v_prec_619_);
return v___x_925_;
}
}
}
}
case 15:
{
lean_object* v_target_932_; lean_object* v___y_934_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_target_932_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_target_932_);
lean_dec_ref(v_x_618_);
v___x_943_ = lean_unsigned_to_nat(1024u);
v___x_944_ = lean_nat_dec_le(v___x_943_, v_prec_619_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_934_ = v___x_945_;
goto v___jp_933_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_934_ = v___x_946_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_935_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__53));
v___x_936_ = lean_unsigned_to_nat(1024u);
v___x_937_ = l_Lean_Name_reprPrec(v_target_932_, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_935_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
lean_inc(v___y_934_);
v___x_939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_939_, 0, v___y_934_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = 0;
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_940_);
v___x_942_ = l_Repr_addAppParen(v___x_941_, v_prec_619_);
return v___x_942_;
}
}
case 16:
{
lean_object* v_pkg_947_; lean_object* v_mod_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_972_; 
v_pkg_947_ = lean_ctor_get(v_x_618_, 0);
v_mod_948_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_972_ == 0)
{
v___x_950_ = v_x_618_;
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_mod_948_);
lean_inc(v_pkg_947_);
lean_dec(v_x_618_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___y_953_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1024u);
v___x_969_ = lean_nat_dec_le(v___x_968_, v_prec_619_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_953_ = v___x_970_;
goto v___jp_952_;
}
else
{
lean_object* v___x_971_; 
v___x_971_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_953_ = v___x_971_;
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_954_ = lean_box(1);
v___x_955_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__56));
v___x_956_ = lean_unsigned_to_nat(1024u);
v___x_957_ = l_Lean_Name_reprPrec(v_pkg_947_, v___x_956_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 5);
lean_ctor_set(v___x_950_, 1, v___x_957_);
lean_ctor_set(v___x_950_, 0, v___x_955_);
v___x_959_ = v___x_950_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_957_);
v___x_959_ = v_reuseFailAlloc_967_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_954_);
v___x_961_ = l_Lean_Name_reprPrec(v_mod_948_, v___x_956_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
lean_inc(v___y_953_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___y_953_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = 0;
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_964_);
v___x_966_ = l_Repr_addAppParen(v___x_965_, v_prec_619_);
return v___x_966_;
}
}
}
}
case 17:
{
lean_object* v_pkg_973_; lean_object* v_spec_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_999_; 
v_pkg_973_ = lean_ctor_get(v_x_618_, 0);
v_spec_974_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_999_ == 0)
{
v___x_976_ = v_x_618_;
v_isShared_977_ = v_isSharedCheck_999_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_spec_974_);
lean_inc(v_pkg_973_);
lean_dec(v_x_618_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_999_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___y_979_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(1024u);
v___x_996_ = lean_nat_dec_le(v___x_995_, v_prec_619_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_979_ = v___x_997_;
goto v___jp_978_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_979_ = v___x_998_;
goto v___jp_978_;
}
v___jp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_980_ = lean_box(1);
v___x_981_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__59));
v___x_982_ = lean_unsigned_to_nat(1024u);
v___x_983_ = l_Lean_Name_reprPrec(v_pkg_973_, v___x_982_);
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 5);
lean_ctor_set(v___x_976_, 1, v___x_983_);
lean_ctor_set(v___x_976_, 0, v___x_981_);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_983_);
v___x_985_ = v_reuseFailAlloc_994_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_980_);
v___x_987_ = l_String_quote(v_spec_974_);
v___x_988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_inc(v___y_979_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_979_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = 0;
v___x_992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_991_);
v___x_993_ = l_Repr_addAppParen(v___x_992_, v_prec_619_);
return v___x_993_;
}
}
}
}
case 18:
{
lean_object* v_key_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1020_; 
v_key_1000_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1002_ = v_x_618_;
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_key_1000_);
lean_dec(v_x_618_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___y_1005_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1024u);
v___x_1017_ = lean_nat_dec_le(v___x_1016_, v_prec_619_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1005_ = v___x_1018_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1005_ = v___x_1019_;
goto v___jp_1004_;
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1006_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__62));
v___x_1007_ = l_String_quote(v_key_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 3);
lean_ctor_set(v___x_1002_, 0, v___x_1007_);
v___x_1009_ = v___x_1002_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1006_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc(v___y_1005_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___y_1005_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_1012_);
v___x_1014_ = l_Repr_addAppParen(v___x_1013_, v_prec_619_);
return v___x_1014_;
}
}
}
}
case 19:
{
lean_object* v_spec_1021_; uint32_t v_tooMany_1022_; lean_object* v___y_1024_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_spec_1021_ = lean_ctor_get(v_x_618_, 0);
lean_inc_ref(v_spec_1021_);
v_tooMany_1022_ = lean_ctor_get_uint32(v_x_618_, sizeof(void*)*1);
lean_dec_ref(v_x_618_);
v___x_1038_ = lean_unsigned_to_nat(1024u);
v___x_1039_ = lean_nat_dec_le(v___x_1038_, v_prec_619_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1024_ = v___x_1040_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1024_ = v___x_1041_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1025_ = lean_box(1);
v___x_1026_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__65));
v___x_1027_ = l_String_quote(v_spec_1021_);
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1026_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1025_);
v___x_1031_ = l_Char_quote(v_tooMany_1022_);
v___x_1032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1030_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_inc(v___y_1024_);
v___x_1034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___y_1024_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = 0;
v___x_1036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_1035_);
v___x_1037_ = l_Repr_addAppParen(v___x_1036_, v_prec_619_);
return v___x_1037_;
}
}
case 20:
{
lean_object* v_target_1042_; lean_object* v_facet_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1067_; 
v_target_1042_ = lean_ctor_get(v_x_618_, 0);
v_facet_1043_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1045_ = v_x_618_;
v_isShared_1046_ = v_isSharedCheck_1067_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_facet_1043_);
lean_inc(v_target_1042_);
lean_dec(v_x_618_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1067_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___y_1048_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1024u);
v___x_1064_ = lean_nat_dec_le(v___x_1063_, v_prec_619_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1048_ = v___x_1065_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1048_ = v___x_1066_;
goto v___jp_1047_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1049_ = lean_box(1);
v___x_1050_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__68));
v___x_1051_ = lean_unsigned_to_nat(1024u);
v___x_1052_ = l_Lean_Name_reprPrec(v_target_1042_, v___x_1051_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 5);
lean_ctor_set(v___x_1045_, 1, v___x_1052_);
lean_ctor_set(v___x_1045_, 0, v___x_1050_);
v___x_1054_ = v___x_1045_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1049_);
v___x_1056_ = l_Lean_Name_reprPrec(v_facet_1043_, v___x_1051_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
lean_inc(v___y_1048_);
v___x_1058_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___y_1048_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = 0;
v___x_1060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*1, v___x_1059_);
v___x_1061_ = l_Repr_addAppParen(v___x_1060_, v_prec_619_);
return v___x_1061_;
}
}
}
}
case 21:
{
lean_object* v_spec_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1088_; 
v_spec_1068_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1070_ = v_x_618_;
v_isShared_1071_ = v_isSharedCheck_1088_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_spec_1068_);
lean_dec(v_x_618_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1088_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___y_1073_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(1024u);
v___x_1085_ = lean_nat_dec_le(v___x_1084_, v_prec_619_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1073_ = v___x_1086_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1073_ = v___x_1087_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__71));
v___x_1075_ = l_String_quote(v_spec_1068_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 3);
lean_ctor_set(v___x_1070_, 0, v___x_1075_);
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
lean_inc(v___y_1073_);
v___x_1079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___y_1073_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = 0;
v___x_1081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*1, v___x_1080_);
v___x_1082_ = l_Repr_addAppParen(v___x_1081_, v_prec_619_);
return v___x_1082_;
}
}
}
}
case 22:
{
lean_object* v_script_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1109_; 
v_script_1089_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1091_ = v_x_618_;
v_isShared_1092_ = v_isSharedCheck_1109_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_script_1089_);
lean_dec(v_x_618_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1109_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___y_1094_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(1024u);
v___x_1106_ = lean_nat_dec_le(v___x_1105_, v_prec_619_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1094_ = v___x_1107_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1094_ = v___x_1108_;
goto v___jp_1093_;
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__74));
v___x_1096_ = l_String_quote(v_script_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 3);
lean_ctor_set(v___x_1091_, 0, v___x_1096_);
v___x_1098_ = v___x_1091_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
lean_inc(v___y_1094_);
v___x_1100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___y_1094_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = 0;
v___x_1102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*1, v___x_1101_);
v___x_1103_ = l_Repr_addAppParen(v___x_1102_, v_prec_619_);
return v___x_1103_;
}
}
}
}
case 23:
{
lean_object* v_script_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1130_; 
v_script_1110_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1112_ = v_x_618_;
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_script_1110_);
lean_dec(v_x_618_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___y_1115_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(1024u);
v___x_1127_ = lean_nat_dec_le(v___x_1126_, v_prec_619_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1115_ = v___x_1128_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1115_ = v___x_1129_;
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__77));
v___x_1117_ = l_String_quote(v_script_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 3);
lean_ctor_set(v___x_1112_, 0, v___x_1117_);
v___x_1119_ = v___x_1112_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1116_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_inc(v___y_1115_);
v___x_1121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1115_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = 0;
v___x_1123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*1, v___x_1122_);
v___x_1124_ = l_Repr_addAppParen(v___x_1123_, v_prec_619_);
return v___x_1124_;
}
}
}
}
case 24:
{
lean_object* v_spec_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1151_; 
v_spec_1131_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1133_ = v_x_618_;
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_spec_1131_);
lean_dec(v_x_618_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___y_1136_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(1024u);
v___x_1148_ = lean_nat_dec_le(v___x_1147_, v_prec_619_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1136_ = v___x_1149_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1136_ = v___x_1150_;
goto v___jp_1135_;
}
v___jp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__80));
v___x_1138_ = l_String_quote(v_spec_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 3);
lean_ctor_set(v___x_1133_, 0, v___x_1138_);
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1137_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
lean_inc(v___y_1136_);
v___x_1142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1136_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = 0;
v___x_1144_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*1, v___x_1143_);
v___x_1145_ = l_Repr_addAppParen(v___x_1144_, v_prec_619_);
return v___x_1145_;
}
}
}
}
case 25:
{
lean_object* v_path_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1176_; 
v_path_1152_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1154_ = v_x_618_;
v_isShared_1155_ = v_isSharedCheck_1176_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_path_1152_);
lean_dec(v_x_618_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1176_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___y_1157_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(1024u);
v___x_1173_ = lean_nat_dec_le(v___x_1172_, v_prec_619_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1157_ = v___x_1174_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1157_ = v___x_1175_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1158_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__83));
v___x_1159_ = lean_unsigned_to_nat(1024u);
v___x_1160_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_1161_ = l_String_quote(v_path_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 3);
lean_ctor_set(v___x_1154_, 0, v___x_1161_);
v___x_1163_ = v___x_1154_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1160_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Repr_addAppParen(v___x_1164_, v___x_1159_);
v___x_1166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1158_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
lean_inc(v___y_1157_);
v___x_1167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___y_1157_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = 0;
v___x_1169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set_uint8(v___x_1169_, sizeof(void*)*1, v___x_1168_);
v___x_1170_ = l_Repr_addAppParen(v___x_1169_, v_prec_619_);
return v___x_1170_;
}
}
}
}
case 26:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(1024u);
v___x_1178_ = lean_nat_dec_le(v___x_1177_, v_prec_619_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_628_ = v___x_1179_;
goto v___jp_627_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_628_ = v___x_1180_;
goto v___jp_627_;
}
}
case 27:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_unsigned_to_nat(1024u);
v___x_1182_ = lean_nat_dec_le(v___x_1181_, v_prec_619_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_621_ = v___x_1183_;
goto v___jp_620_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_621_ = v___x_1184_;
goto v___jp_620_;
}
}
case 28:
{
lean_object* v_expected_1185_; lean_object* v_actual_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1211_; 
v_expected_1185_ = lean_ctor_get(v_x_618_, 0);
v_actual_1186_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1188_ = v_x_618_;
v_isShared_1189_ = v_isSharedCheck_1211_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_actual_1186_);
lean_inc(v_expected_1185_);
lean_dec(v_x_618_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1211_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___y_1191_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(1024u);
v___x_1208_ = lean_nat_dec_le(v___x_1207_, v_prec_619_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1191_ = v___x_1209_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1191_ = v___x_1210_;
goto v___jp_1190_;
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1192_ = lean_box(1);
v___x_1193_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__86));
v___x_1194_ = l_String_quote(v_expected_1185_);
v___x_1195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 5);
lean_ctor_set(v___x_1188_, 1, v___x_1195_);
lean_ctor_set(v___x_1188_, 0, v___x_1193_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1192_);
v___x_1199_ = l_String_quote(v_actual_1186_);
v___x_1200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1198_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
lean_inc(v___y_1191_);
v___x_1202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1191_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = 0;
v___x_1204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*1, v___x_1203_);
v___x_1205_ = l_Repr_addAppParen(v___x_1204_, v_prec_619_);
return v___x_1205_;
}
}
}
}
case 29:
{
lean_object* v_msg_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1232_; 
v_msg_1212_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1214_ = v_x_618_;
v_isShared_1215_ = v_isSharedCheck_1232_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_msg_1212_);
lean_dec(v_x_618_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1232_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___y_1217_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(1024u);
v___x_1229_ = lean_nat_dec_le(v___x_1228_, v_prec_619_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1217_ = v___x_1230_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1217_ = v___x_1231_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1218_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__89));
v___x_1219_ = l_String_quote(v_msg_1212_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 3);
lean_ctor_set(v___x_1214_, 0, v___x_1219_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1218_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
lean_inc(v___y_1217_);
v___x_1223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1217_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = 0;
v___x_1225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*1, v___x_1224_);
v___x_1226_ = l_Repr_addAppParen(v___x_1225_, v_prec_619_);
return v___x_1226_;
}
}
}
}
default: 
{
lean_object* v_path_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1257_; 
v_path_1233_ = lean_ctor_get(v_x_618_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1235_ = v_x_618_;
v_isShared_1236_ = v_isSharedCheck_1257_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_path_1233_);
lean_dec(v_x_618_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1257_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___y_1238_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_unsigned_to_nat(1024u);
v___x_1254_ = lean_nat_dec_le(v___x_1253_, v_prec_619_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1238_ = v___x_1255_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1238_ = v___x_1256_;
goto v___jp_1237_;
}
v___jp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__92));
v___x_1240_ = lean_unsigned_to_nat(1024u);
v___x_1241_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_1242_ = l_String_quote(v_path_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set_tag(v___x_1235_, 3);
lean_ctor_set(v___x_1235_, 0, v___x_1242_);
v___x_1244_ = v___x_1235_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1241_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Repr_addAppParen(v___x_1245_, v___x_1240_);
v___x_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1239_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
lean_inc(v___y_1238_);
v___x_1248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___y_1238_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = 0;
v___x_1250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*1, v___x_1249_);
v___x_1251_ = l_Repr_addAppParen(v___x_1250_, v_prec_619_);
return v___x_1251_;
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__1));
lean_inc(v___y_621_);
v___x_623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_623_, 0, v___y_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = 0;
v___x_625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*1, v___x_624_);
v___x_626_ = l_Repr_addAppParen(v___x_625_, v_prec_619_);
return v___x_626_;
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__3));
lean_inc(v___y_628_);
v___x_630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_630_, 0, v___y_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = 0;
v___x_632_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_631_);
v___x_633_ = l_Repr_addAppParen(v___x_632_, v_prec_619_);
return v___x_633_;
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__5));
lean_inc(v___y_635_);
v___x_637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_637_, 0, v___y_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = 0;
v___x_639_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*1, v___x_638_);
v___x_640_ = l_Repr_addAppParen(v___x_639_, v_prec_619_);
return v___x_640_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_643_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__7));
lean_inc(v___y_642_);
v___x_644_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = 0;
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_645_);
v___x_647_ = l_Repr_addAppParen(v___x_646_, v_prec_619_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr___boxed(lean_object* v_x_1258_, lean_object* v_prec_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lake_instReprCliError_repr(v_x_1258_, v_prec_1259_);
lean_dec(v_prec_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__1(lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_nat_to_int(v_a_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(lean_object* v_a_1263_, lean_object* v_n_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(v_a_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___boxed(lean_object* v_a_1266_, lean_object* v_n_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(v_a_1266_, v_n_1267_);
lean_dec(v_n_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object* v_x_1315_){
_start:
{
switch(lean_obj_tag(v_x_1315_))
{
case 0:
{
lean_object* v___x_1316_; 
v___x_1316_ = ((lean_object*)(l_Lake_CliError_toString___closed__0));
return v___x_1316_;
}
case 1:
{
lean_object* v_cmd_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_cmd_1317_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_cmd_1317_);
lean_dec_ref(v_x_1315_);
v___x_1318_ = ((lean_object*)(l_Lake_CliError_toString___closed__1));
v___x_1319_ = lean_string_append(v___x_1318_, v_cmd_1317_);
lean_dec_ref(v_cmd_1317_);
v___x_1320_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
return v___x_1321_;
}
case 2:
{
lean_object* v_arg_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_arg_1322_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_arg_1322_);
lean_dec_ref(v_x_1315_);
v___x_1323_ = ((lean_object*)(l_Lake_CliError_toString___closed__3));
v___x_1324_ = lean_string_append(v___x_1323_, v_arg_1322_);
lean_dec_ref(v_arg_1322_);
return v___x_1324_;
}
case 3:
{
lean_object* v_opt_1325_; lean_object* v_arg_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_opt_1325_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_opt_1325_);
v_arg_1326_ = lean_ctor_get(v_x_1315_, 1);
lean_inc_ref(v_arg_1326_);
lean_dec_ref(v_x_1315_);
v___x_1327_ = ((lean_object*)(l_Lake_CliError_toString___closed__3));
v___x_1328_ = lean_string_append(v___x_1327_, v_arg_1326_);
lean_dec_ref(v_arg_1326_);
v___x_1329_ = ((lean_object*)(l_Lake_CliError_toString___closed__4));
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
v___x_1331_ = lean_string_append(v___x_1330_, v_opt_1325_);
lean_dec_ref(v_opt_1325_);
return v___x_1331_;
}
case 4:
{
lean_object* v_opt_1332_; lean_object* v_arg_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_opt_1332_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_opt_1332_);
v_arg_1333_ = lean_ctor_get(v_x_1315_, 1);
lean_inc_ref(v_arg_1333_);
lean_dec_ref(v_x_1315_);
v___x_1334_ = ((lean_object*)(l_Lake_CliError_toString___closed__5));
v___x_1335_ = lean_string_append(v___x_1334_, v_opt_1332_);
lean_dec_ref(v_opt_1332_);
v___x_1336_ = ((lean_object*)(l_Lake_CliError_toString___closed__6));
v___x_1337_ = lean_string_append(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_string_append(v___x_1337_, v_arg_1333_);
lean_dec_ref(v_arg_1333_);
return v___x_1338_;
}
case 5:
{
uint32_t v_opt_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_opt_1339_ = lean_ctor_get_uint32(v_x_1315_, 0);
lean_dec_ref(v_x_1315_);
v___x_1340_ = ((lean_object*)(l_Lake_CliError_toString___closed__7));
v___x_1341_ = ((lean_object*)(l_Lake_CliError_toString___closed__8));
v___x_1342_ = lean_string_push(v___x_1341_, v_opt_1339_);
v___x_1343_ = lean_string_append(v___x_1340_, v___x_1342_);
lean_dec_ref(v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
return v___x_1345_;
}
case 6:
{
lean_object* v_opt_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_opt_1346_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_opt_1346_);
lean_dec_ref(v_x_1315_);
v___x_1347_ = ((lean_object*)(l_Lake_CliError_toString___closed__9));
v___x_1348_ = lean_string_append(v___x_1347_, v_opt_1346_);
lean_dec_ref(v_opt_1346_);
v___x_1349_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
return v___x_1350_;
}
case 7:
{
lean_object* v_args_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_args_1351_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_args_1351_);
lean_dec_ref(v_x_1315_);
v___x_1352_ = ((lean_object*)(l_Lake_CliError_toString___closed__10));
v___x_1353_ = ((lean_object*)(l_Lake_CliError_toString___closed__11));
v___x_1354_ = l_String_intercalate(v___x_1353_, v_args_1351_);
v___x_1355_ = lean_string_append(v___x_1352_, v___x_1354_);
lean_dec_ref(v___x_1354_);
return v___x_1355_;
}
case 8:
{
lean_object* v___x_1356_; 
v___x_1356_ = ((lean_object*)(l_Lake_CliError_toString___closed__12));
return v___x_1356_;
}
case 9:
{
lean_object* v_spec_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_spec_1357_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1357_);
lean_dec_ref(v_x_1315_);
v___x_1358_ = ((lean_object*)(l_Lake_CliError_toString___closed__13));
v___x_1359_ = lean_string_append(v___x_1358_, v_spec_1357_);
lean_dec_ref(v_spec_1357_);
v___x_1360_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
return v___x_1361_;
}
case 10:
{
lean_object* v_spec_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_spec_1362_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1362_);
lean_dec_ref(v_x_1315_);
v___x_1363_ = ((lean_object*)(l_Lake_CliError_toString___closed__15));
v___x_1364_ = lean_string_append(v___x_1363_, v_spec_1362_);
lean_dec_ref(v_spec_1362_);
v___x_1365_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
return v___x_1366_;
}
case 11:
{
lean_object* v_mod_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_mod_1367_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_mod_1367_);
lean_dec_ref(v_x_1315_);
v___x_1368_ = ((lean_object*)(l_Lake_CliError_toString___closed__16));
v___x_1369_ = 0;
v___x_1370_ = l_Lean_Name_toString(v_mod_1367_, v___x_1369_);
v___x_1371_ = lean_string_append(v___x_1368_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
return v___x_1373_;
}
case 12:
{
lean_object* v_path_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_path_1374_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_path_1374_);
lean_dec_ref(v_x_1315_);
v___x_1375_ = ((lean_object*)(l_Lake_CliError_toString___closed__17));
v___x_1376_ = lean_string_append(v___x_1375_, v_path_1374_);
lean_dec_ref(v_path_1374_);
v___x_1377_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
return v___x_1378_;
}
case 13:
{
lean_object* v_spec_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_spec_1379_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1379_);
lean_dec_ref(v_x_1315_);
v___x_1380_ = ((lean_object*)(l_Lake_CliError_toString___closed__18));
v___x_1381_ = lean_string_append(v___x_1380_, v_spec_1379_);
lean_dec_ref(v_spec_1379_);
v___x_1382_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
return v___x_1383_;
}
case 14:
{
lean_object* v_type_1384_; lean_object* v_facet_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_type_1384_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_type_1384_);
v_facet_1385_ = lean_ctor_get(v_x_1315_, 1);
lean_inc(v_facet_1385_);
lean_dec_ref(v_x_1315_);
v___x_1386_ = ((lean_object*)(l_Lake_CliError_toString___closed__19));
v___x_1387_ = lean_string_append(v___x_1386_, v_type_1384_);
lean_dec_ref(v_type_1384_);
v___x_1388_ = ((lean_object*)(l_Lake_CliError_toString___closed__20));
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
v___x_1390_ = 0;
v___x_1391_ = l_Lean_Name_toString(v_facet_1385_, v___x_1390_);
v___x_1392_ = lean_string_append(v___x_1389_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
return v___x_1394_;
}
case 15:
{
lean_object* v_target_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_target_1395_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_target_1395_);
lean_dec_ref(v_x_1315_);
v___x_1396_ = ((lean_object*)(l_Lake_CliError_toString___closed__21));
v___x_1397_ = 0;
v___x_1398_ = l_Lean_Name_toString(v_target_1395_, v___x_1397_);
v___x_1399_ = lean_string_append(v___x_1396_, v___x_1398_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
return v___x_1401_;
}
case 16:
{
lean_object* v_pkg_1402_; lean_object* v_mod_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_pkg_1402_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_pkg_1402_);
v_mod_1403_ = lean_ctor_get(v_x_1315_, 1);
lean_inc(v_mod_1403_);
lean_dec_ref(v_x_1315_);
v___x_1404_ = ((lean_object*)(l_Lake_CliError_toString___closed__22));
v___x_1405_ = 0;
v___x_1406_ = l_Lean_Name_toString(v_pkg_1402_, v___x_1405_);
v___x_1407_ = lean_string_append(v___x_1404_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lake_CliError_toString___closed__23));
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = l_Lean_Name_toString(v_mod_1403_, v___x_1405_);
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
return v___x_1413_;
}
case 17:
{
lean_object* v_pkg_1414_; lean_object* v_spec_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_pkg_1414_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_pkg_1414_);
v_spec_1415_ = lean_ctor_get(v_x_1315_, 1);
lean_inc_ref(v_spec_1415_);
lean_dec_ref(v_x_1315_);
v___x_1416_ = ((lean_object*)(l_Lake_CliError_toString___closed__22));
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Name_toString(v_pkg_1414_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1416_, v___x_1418_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lake_CliError_toString___closed__24));
v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
v___x_1422_ = lean_string_append(v___x_1421_, v_spec_1415_);
lean_dec_ref(v_spec_1415_);
v___x_1423_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
return v___x_1424_;
}
case 18:
{
lean_object* v_key_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_key_1425_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_key_1425_);
lean_dec_ref(v_x_1315_);
v___x_1426_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1427_ = lean_string_append(v___x_1426_, v_key_1425_);
lean_dec_ref(v_key_1425_);
v___x_1428_ = ((lean_object*)(l_Lake_CliError_toString___closed__25));
v___x_1429_ = lean_string_append(v___x_1427_, v___x_1428_);
return v___x_1429_;
}
case 19:
{
lean_object* v_spec_1430_; uint32_t v_tooMany_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_spec_1430_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1430_);
v_tooMany_1431_ = lean_ctor_get_uint32(v_x_1315_, sizeof(void*)*1);
lean_dec_ref(v_x_1315_);
v___x_1432_ = ((lean_object*)(l_Lake_CliError_toString___closed__26));
v___x_1433_ = lean_string_append(v___x_1432_, v_spec_1430_);
lean_dec_ref(v_spec_1430_);
v___x_1434_ = ((lean_object*)(l_Lake_CliError_toString___closed__27));
v___x_1435_ = lean_string_append(v___x_1433_, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lake_CliError_toString___closed__8));
v___x_1437_ = lean_string_push(v___x_1436_, v_tooMany_1431_);
v___x_1438_ = lean_string_append(v___x_1435_, v___x_1437_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lake_CliError_toString___closed__28));
v___x_1440_ = lean_string_append(v___x_1438_, v___x_1439_);
return v___x_1440_;
}
case 20:
{
lean_object* v_target_1441_; lean_object* v_facet_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_target_1441_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_target_1441_);
v_facet_1442_ = lean_ctor_get(v_x_1315_, 1);
lean_inc(v_facet_1442_);
lean_dec_ref(v_x_1315_);
v___x_1443_ = ((lean_object*)(l_Lake_CliError_toString___closed__29));
v___x_1444_ = 0;
v___x_1445_ = l_Lean_Name_toString(v_facet_1442_, v___x_1444_);
v___x_1446_ = lean_string_append(v___x_1443_, v___x_1445_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lake_CliError_toString___closed__30));
v___x_1448_ = lean_string_append(v___x_1446_, v___x_1447_);
v___x_1449_ = l_Lean_Name_toString(v_target_1441_, v___x_1444_);
v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lake_CliError_toString___closed__31));
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
return v___x_1452_;
}
case 21:
{
lean_object* v_spec_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_spec_1453_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1453_);
lean_dec_ref(v_x_1315_);
v___x_1454_ = ((lean_object*)(l_Lake_CliError_toString___closed__32));
v___x_1455_ = lean_string_append(v___x_1454_, v_spec_1453_);
lean_dec_ref(v_spec_1453_);
return v___x_1455_;
}
case 22:
{
lean_object* v_script_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_script_1456_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_script_1456_);
lean_dec_ref(v_x_1315_);
v___x_1457_ = ((lean_object*)(l_Lake_CliError_toString___closed__33));
v___x_1458_ = lean_string_append(v___x_1457_, v_script_1456_);
lean_dec_ref(v_script_1456_);
return v___x_1458_;
}
case 23:
{
lean_object* v_script_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_script_1459_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_script_1459_);
lean_dec_ref(v_x_1315_);
v___x_1460_ = ((lean_object*)(l_Lake_CliError_toString___closed__34));
v___x_1461_ = lean_string_append(v___x_1460_, v_script_1459_);
lean_dec_ref(v_script_1459_);
v___x_1462_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
return v___x_1463_;
}
case 24:
{
lean_object* v_spec_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_spec_1464_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_spec_1464_);
lean_dec_ref(v_x_1315_);
v___x_1465_ = ((lean_object*)(l_Lake_CliError_toString___closed__35));
v___x_1466_ = lean_string_append(v___x_1465_, v_spec_1464_);
lean_dec_ref(v_spec_1464_);
v___x_1467_ = ((lean_object*)(l_Lake_CliError_toString___closed__36));
v___x_1468_ = lean_string_append(v___x_1466_, v___x_1467_);
return v___x_1468_;
}
case 25:
{
lean_object* v_path_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_path_1469_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_path_1469_);
lean_dec_ref(v_x_1315_);
v___x_1470_ = ((lean_object*)(l_Lake_CliError_toString___closed__37));
v___x_1471_ = lean_string_append(v___x_1470_, v_path_1469_);
lean_dec_ref(v_path_1469_);
return v___x_1471_;
}
case 26:
{
lean_object* v___x_1472_; 
v___x_1472_ = ((lean_object*)(l_Lake_CliError_toString___closed__38));
return v___x_1472_;
}
case 27:
{
lean_object* v___x_1473_; 
v___x_1473_ = ((lean_object*)(l_Lake_CliError_toString___closed__39));
return v___x_1473_;
}
case 28:
{
lean_object* v_expected_1474_; lean_object* v_actual_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_expected_1474_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_expected_1474_);
v_actual_1475_ = lean_ctor_get(v_x_1315_, 1);
lean_inc_ref(v_actual_1475_);
lean_dec_ref(v_x_1315_);
v___x_1476_ = ((lean_object*)(l_Lake_CliError_toString___closed__40));
v___x_1477_ = lean_string_append(v___x_1476_, v_expected_1474_);
lean_dec_ref(v_expected_1474_);
v___x_1478_ = ((lean_object*)(l_Lake_CliError_toString___closed__41));
v___x_1479_ = lean_string_append(v___x_1477_, v___x_1478_);
v___x_1480_ = lean_string_utf8_byte_size(v_actual_1475_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_nat_dec_eq(v___x_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_string_append(v___x_1479_, v_actual_1475_);
lean_dec_ref(v_actual_1475_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_actual_1475_);
v___x_1484_ = ((lean_object*)(l_Lake_CliError_toString___closed__42));
v___x_1485_ = lean_string_append(v___x_1479_, v___x_1484_);
return v___x_1485_;
}
}
case 29:
{
lean_object* v_msg_1486_; 
v_msg_1486_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_msg_1486_);
lean_dec_ref(v_x_1315_);
return v_msg_1486_;
}
default: 
{
lean_object* v_path_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_path_1487_ = lean_ctor_get(v_x_1315_, 0);
lean_inc_ref(v_path_1487_);
lean_dec_ref(v_x_1315_);
v___x_1488_ = ((lean_object*)(l_Lake_CliError_toString___closed__43));
v___x_1489_ = lean_string_append(v___x_1488_, v_path_1487_);
lean_dec_ref(v_path_1487_);
return v___x_1489_;
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
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin);
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
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Error(builtin);
}
#ifdef __cplusplus
}
#endif

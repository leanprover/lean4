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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_CliError_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 1:
{
lean_object* v_cmd_7_; lean_object* v___x_8_; 
v_cmd_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_cmd_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_cmd_7_);
return v___x_8_;
}
case 2:
{
lean_object* v_arg_9_; lean_object* v___x_10_; 
v_arg_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_arg_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_arg_9_);
return v___x_10_;
}
case 3:
{
lean_object* v_opt_11_; lean_object* v_arg_12_; lean_object* v___x_13_; 
v_opt_11_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_opt_11_);
v_arg_12_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_arg_12_);
lean_dec_ref_known(v_t_5_, 2);
v___x_13_ = lean_apply_2(v_k_6_, v_opt_11_, v_arg_12_);
return v___x_13_;
}
case 4:
{
lean_object* v_opt_14_; lean_object* v_arg_15_; lean_object* v___x_16_; 
v_opt_14_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_opt_14_);
v_arg_15_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_arg_15_);
lean_dec_ref_known(v_t_5_, 2);
v___x_16_ = lean_apply_2(v_k_6_, v_opt_14_, v_arg_15_);
return v___x_16_;
}
case 5:
{
uint32_t v_opt_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_opt_17_ = lean_ctor_get_uint32(v_t_5_, 0);
lean_dec_ref_known(v_t_5_, 0);
v___x_18_ = lean_box_uint32(v_opt_17_);
v___x_19_ = lean_apply_1(v_k_6_, v___x_18_);
return v___x_19_;
}
case 6:
{
lean_object* v_opt_20_; lean_object* v___x_21_; 
v_opt_20_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_opt_20_);
lean_dec_ref_known(v_t_5_, 1);
v___x_21_ = lean_apply_1(v_k_6_, v_opt_20_);
return v___x_21_;
}
case 7:
{
lean_object* v_args_22_; lean_object* v___x_23_; 
v_args_22_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_args_22_);
lean_dec_ref_known(v_t_5_, 1);
v___x_23_ = lean_apply_1(v_k_6_, v_args_22_);
return v___x_23_;
}
case 9:
{
lean_object* v_spec_24_; lean_object* v___x_25_; 
v_spec_24_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_24_);
lean_dec_ref_known(v_t_5_, 1);
v___x_25_ = lean_apply_1(v_k_6_, v_spec_24_);
return v___x_25_;
}
case 10:
{
lean_object* v_spec_26_; lean_object* v___x_27_; 
v_spec_26_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_26_);
lean_dec_ref_known(v_t_5_, 1);
v___x_27_ = lean_apply_1(v_k_6_, v_spec_26_);
return v___x_27_;
}
case 11:
{
lean_object* v_mod_28_; lean_object* v___x_29_; 
v_mod_28_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_mod_28_);
lean_dec_ref_known(v_t_5_, 1);
v___x_29_ = lean_apply_1(v_k_6_, v_mod_28_);
return v___x_29_;
}
case 12:
{
lean_object* v_path_30_; lean_object* v___x_31_; 
v_path_30_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_path_30_);
lean_dec_ref_known(v_t_5_, 1);
v___x_31_ = lean_apply_1(v_k_6_, v_path_30_);
return v___x_31_;
}
case 13:
{
lean_object* v_spec_32_; lean_object* v___x_33_; 
v_spec_32_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_32_);
lean_dec_ref_known(v_t_5_, 1);
v___x_33_ = lean_apply_1(v_k_6_, v_spec_32_);
return v___x_33_;
}
case 14:
{
lean_object* v_type_34_; lean_object* v_facet_35_; lean_object* v___x_36_; 
v_type_34_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_type_34_);
v_facet_35_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_facet_35_);
lean_dec_ref_known(v_t_5_, 2);
v___x_36_ = lean_apply_2(v_k_6_, v_type_34_, v_facet_35_);
return v___x_36_;
}
case 15:
{
lean_object* v_target_37_; lean_object* v___x_38_; 
v_target_37_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_target_37_);
lean_dec_ref_known(v_t_5_, 1);
v___x_38_ = lean_apply_1(v_k_6_, v_target_37_);
return v___x_38_;
}
case 16:
{
lean_object* v_pkg_39_; lean_object* v_mod_40_; lean_object* v___x_41_; 
v_pkg_39_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_pkg_39_);
v_mod_40_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_mod_40_);
lean_dec_ref_known(v_t_5_, 2);
v___x_41_ = lean_apply_2(v_k_6_, v_pkg_39_, v_mod_40_);
return v___x_41_;
}
case 17:
{
lean_object* v_pkg_42_; lean_object* v_spec_43_; lean_object* v___x_44_; 
v_pkg_42_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_pkg_42_);
v_spec_43_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_spec_43_);
lean_dec_ref_known(v_t_5_, 2);
v___x_44_ = lean_apply_2(v_k_6_, v_pkg_42_, v_spec_43_);
return v___x_44_;
}
case 18:
{
lean_object* v_key_45_; lean_object* v___x_46_; 
v_key_45_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_key_45_);
lean_dec_ref_known(v_t_5_, 1);
v___x_46_ = lean_apply_1(v_k_6_, v_key_45_);
return v___x_46_;
}
case 19:
{
lean_object* v_spec_47_; uint32_t v_tooMany_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_spec_47_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_47_);
v_tooMany_48_ = lean_ctor_get_uint32(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_49_ = lean_box_uint32(v_tooMany_48_);
v___x_50_ = lean_apply_2(v_k_6_, v_spec_47_, v___x_49_);
return v___x_50_;
}
case 20:
{
lean_object* v_target_51_; lean_object* v_facet_52_; lean_object* v___x_53_; 
v_target_51_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_target_51_);
v_facet_52_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_facet_52_);
lean_dec_ref_known(v_t_5_, 2);
v___x_53_ = lean_apply_2(v_k_6_, v_target_51_, v_facet_52_);
return v___x_53_;
}
case 21:
{
lean_object* v_spec_54_; lean_object* v___x_55_; 
v_spec_54_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_54_);
lean_dec_ref_known(v_t_5_, 1);
v___x_55_ = lean_apply_1(v_k_6_, v_spec_54_);
return v___x_55_;
}
case 22:
{
lean_object* v_script_56_; lean_object* v___x_57_; 
v_script_56_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_script_56_);
lean_dec_ref_known(v_t_5_, 1);
v___x_57_ = lean_apply_1(v_k_6_, v_script_56_);
return v___x_57_;
}
case 23:
{
lean_object* v_script_58_; lean_object* v___x_59_; 
v_script_58_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_script_58_);
lean_dec_ref_known(v_t_5_, 1);
v___x_59_ = lean_apply_1(v_k_6_, v_script_58_);
return v___x_59_;
}
case 24:
{
lean_object* v_spec_60_; lean_object* v___x_61_; 
v_spec_60_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_spec_60_);
lean_dec_ref_known(v_t_5_, 1);
v___x_61_ = lean_apply_1(v_k_6_, v_spec_60_);
return v___x_61_;
}
case 25:
{
lean_object* v_path_62_; lean_object* v___x_63_; 
v_path_62_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_path_62_);
lean_dec_ref_known(v_t_5_, 1);
v___x_63_ = lean_apply_1(v_k_6_, v_path_62_);
return v___x_63_;
}
case 28:
{
lean_object* v_expected_64_; lean_object* v_actual_65_; lean_object* v___x_66_; 
v_expected_64_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_expected_64_);
v_actual_65_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_actual_65_);
lean_dec_ref_known(v_t_5_, 2);
v___x_66_ = lean_apply_2(v_k_6_, v_expected_64_, v_actual_65_);
return v___x_66_;
}
case 29:
{
lean_object* v_msg_67_; lean_object* v___x_68_; 
v_msg_67_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_msg_67_);
lean_dec_ref_known(v_t_5_, 1);
v___x_68_ = lean_apply_1(v_k_6_, v_msg_67_);
return v___x_68_;
}
case 30:
{
lean_object* v_path_69_; lean_object* v___x_70_; 
v_path_69_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_path_69_);
lean_dec_ref_known(v_t_5_, 1);
v___x_70_ = lean_apply_1(v_k_6_, v_path_69_);
return v___x_70_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lake_CliError_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_ctorElim___boxed(lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lake_CliError_ctorElim(v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim___redArg(lean_object* v_t_83_, lean_object* v_missingCommand_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lake_CliError_ctorElim___redArg(v_t_83_, v_missingCommand_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingCommand_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_missingCommand_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lake_CliError_ctorElim___redArg(v_t_87_, v_missingCommand_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim___redArg(lean_object* v_t_91_, lean_object* v_unknownCommand_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lake_CliError_ctorElim___redArg(v_t_91_, v_unknownCommand_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownCommand_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_unknownCommand_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_CliError_ctorElim___redArg(v_t_95_, v_unknownCommand_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim___redArg(lean_object* v_t_99_, lean_object* v_missingArg_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lake_CliError_ctorElim___redArg(v_t_99_, v_missingArg_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingArg_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_missingArg_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lake_CliError_ctorElim___redArg(v_t_103_, v_missingArg_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim___redArg(lean_object* v_t_107_, lean_object* v_missingOptArg_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lake_CliError_ctorElim___redArg(v_t_107_, v_missingOptArg_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingOptArg_elim(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_missingOptArg_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lake_CliError_ctorElim___redArg(v_t_111_, v_missingOptArg_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim___redArg(lean_object* v_t_115_, lean_object* v_invalidOptArg_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lake_CliError_ctorElim___redArg(v_t_115_, v_invalidOptArg_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidOptArg_elim(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_invalidOptArg_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lake_CliError_ctorElim___redArg(v_t_119_, v_invalidOptArg_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim___redArg(lean_object* v_t_123_, lean_object* v_unknownShortOption_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lake_CliError_ctorElim___redArg(v_t_123_, v_unknownShortOption_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownShortOption_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_unknownShortOption_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lake_CliError_ctorElim___redArg(v_t_127_, v_unknownShortOption_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim___redArg(lean_object* v_t_131_, lean_object* v_unknownLongOption_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lake_CliError_ctorElim___redArg(v_t_131_, v_unknownLongOption_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLongOption_elim(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_unknownLongOption_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lake_CliError_ctorElim___redArg(v_t_135_, v_unknownLongOption_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim___redArg(lean_object* v_t_139_, lean_object* v_unexpectedArguments_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lake_CliError_ctorElim___redArg(v_t_139_, v_unexpectedArguments_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedArguments_elim(lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_unexpectedArguments_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lake_CliError_ctorElim___redArg(v_t_143_, v_unexpectedArguments_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim___redArg(lean_object* v_t_147_, lean_object* v_unexpectedPlus_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lake_CliError_ctorElim___redArg(v_t_147_, v_unexpectedPlus_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unexpectedPlus_elim(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_unexpectedPlus_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lake_CliError_ctorElim___redArg(v_t_151_, v_unexpectedPlus_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim___redArg(lean_object* v_t_155_, lean_object* v_unknownTemplate_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lake_CliError_ctorElim___redArg(v_t_155_, v_unknownTemplate_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTemplate_elim(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_unknownTemplate_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lake_CliError_ctorElim___redArg(v_t_159_, v_unknownTemplate_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim___redArg(lean_object* v_t_163_, lean_object* v_unknownConfigLang_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lake_CliError_ctorElim___redArg(v_t_163_, v_unknownConfigLang_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownConfigLang_elim(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_unknownConfigLang_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lake_CliError_ctorElim___redArg(v_t_167_, v_unknownConfigLang_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim___redArg(lean_object* v_t_171_, lean_object* v_unknownModule_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lake_CliError_ctorElim___redArg(v_t_171_, v_unknownModule_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModule_elim(lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_unknownModule_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lake_CliError_ctorElim___redArg(v_t_175_, v_unknownModule_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim___redArg(lean_object* v_t_179_, lean_object* v_unknownModulePath_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lake_CliError_ctorElim___redArg(v_t_179_, v_unknownModulePath_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownModulePath_elim(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_unknownModulePath_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lake_CliError_ctorElim___redArg(v_t_183_, v_unknownModulePath_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim___redArg(lean_object* v_t_187_, lean_object* v_unknownPackage_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_CliError_ctorElim___redArg(v_t_187_, v_unknownPackage_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownPackage_elim(lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_unknownPackage_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lake_CliError_ctorElim___redArg(v_t_191_, v_unknownPackage_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim___redArg(lean_object* v_t_195_, lean_object* v_unknownFacet_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lake_CliError_ctorElim___redArg(v_t_195_, v_unknownFacet_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownFacet_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_unknownFacet_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lake_CliError_ctorElim___redArg(v_t_199_, v_unknownFacet_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim___redArg(lean_object* v_t_203_, lean_object* v_unknownTarget_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_CliError_ctorElim___redArg(v_t_203_, v_unknownTarget_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownTarget_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_unknownTarget_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lake_CliError_ctorElim___redArg(v_t_207_, v_unknownTarget_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim___redArg(lean_object* v_t_211_, lean_object* v_missingModule_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lake_CliError_ctorElim___redArg(v_t_211_, v_missingModule_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingModule_elim(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_missingModule_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lake_CliError_ctorElim___redArg(v_t_215_, v_missingModule_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim___redArg(lean_object* v_t_219_, lean_object* v_missingTarget_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lake_CliError_ctorElim___redArg(v_t_219_, v_missingTarget_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingTarget_elim(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_missingTarget_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lake_CliError_ctorElim___redArg(v_t_223_, v_missingTarget_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim___redArg(lean_object* v_t_227_, lean_object* v_invalidBuildTarget_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lake_CliError_ctorElim___redArg(v_t_227_, v_invalidBuildTarget_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidBuildTarget_elim(lean_object* v_motive_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_invalidBuildTarget_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lake_CliError_ctorElim___redArg(v_t_231_, v_invalidBuildTarget_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim___redArg(lean_object* v_t_235_, lean_object* v_invalidTargetSpec_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lake_CliError_ctorElim___redArg(v_t_235_, v_invalidTargetSpec_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidTargetSpec_elim(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_invalidTargetSpec_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lake_CliError_ctorElim___redArg(v_t_239_, v_invalidTargetSpec_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim___redArg(lean_object* v_t_243_, lean_object* v_invalidFacet_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lake_CliError_ctorElim___redArg(v_t_243_, v_invalidFacet_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidFacet_elim(lean_object* v_motive_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_invalidFacet_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lake_CliError_ctorElim___redArg(v_t_247_, v_invalidFacet_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim___redArg(lean_object* v_t_251_, lean_object* v_unknownExe_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lake_CliError_ctorElim___redArg(v_t_251_, v_unknownExe_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownExe_elim(lean_object* v_motive_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_unknownExe_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lake_CliError_ctorElim___redArg(v_t_255_, v_unknownExe_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim___redArg(lean_object* v_t_259_, lean_object* v_unknownScript_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lake_CliError_ctorElim___redArg(v_t_259_, v_unknownScript_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownScript_elim(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_unknownScript_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lake_CliError_ctorElim___redArg(v_t_263_, v_unknownScript_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim___redArg(lean_object* v_t_267_, lean_object* v_missingScriptDoc_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lake_CliError_ctorElim___redArg(v_t_267_, v_missingScriptDoc_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingScriptDoc_elim(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_missingScriptDoc_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lake_CliError_ctorElim___redArg(v_t_271_, v_missingScriptDoc_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim___redArg(lean_object* v_t_275_, lean_object* v_invalidScriptSpec_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lake_CliError_ctorElim___redArg(v_t_275_, v_invalidScriptSpec_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidScriptSpec_elim(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_invalidScriptSpec_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lake_CliError_ctorElim___redArg(v_t_279_, v_invalidScriptSpec_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim___redArg(lean_object* v_t_283_, lean_object* v_outputConfigExists_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lake_CliError_ctorElim___redArg(v_t_283_, v_outputConfigExists_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_outputConfigExists_elim(lean_object* v_motive_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_outputConfigExists_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lake_CliError_ctorElim___redArg(v_t_287_, v_outputConfigExists_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim___redArg(lean_object* v_t_291_, lean_object* v_unknownLeanInstall_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lake_CliError_ctorElim___redArg(v_t_291_, v_unknownLeanInstall_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLeanInstall_elim(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_unknownLeanInstall_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lake_CliError_ctorElim___redArg(v_t_295_, v_unknownLeanInstall_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim___redArg(lean_object* v_t_299_, lean_object* v_unknownLakeInstall_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lake_CliError_ctorElim___redArg(v_t_299_, v_unknownLakeInstall_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_unknownLakeInstall_elim(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_unknownLakeInstall_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lake_CliError_ctorElim___redArg(v_t_303_, v_unknownLakeInstall_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim___redArg(lean_object* v_t_307_, lean_object* v_leanRevMismatch_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lake_CliError_ctorElim___redArg(v_t_307_, v_leanRevMismatch_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_leanRevMismatch_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_leanRevMismatch_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lake_CliError_ctorElim___redArg(v_t_311_, v_leanRevMismatch_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim___redArg(lean_object* v_t_315_, lean_object* v_invalidEnv_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lake_CliError_ctorElim___redArg(v_t_315_, v_invalidEnv_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_invalidEnv_elim(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_invalidEnv_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lake_CliError_ctorElim___redArg(v_t_319_, v_invalidEnv_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim___redArg(lean_object* v_t_323_, lean_object* v_missingRootDir_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lake_CliError_ctorElim___redArg(v_t_323_, v_missingRootDir_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_missingRootDir_elim(lean_object* v_motive_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_missingRootDir_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lake_CliError_ctorElim___redArg(v_t_327_, v_missingRootDir_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError_default(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_box(0);
return v___x_331_;
}
}
static lean_object* _init_l_Lake_instInhabitedCliError(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(lean_object* v___y_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_String_quote(v___y_333_);
v___x_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_dec(v_x_336_);
return v_x_337_;
}
else
{
lean_object* v_head_339_; lean_object* v_tail_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_351_; 
v_head_339_ = lean_ctor_get(v_x_338_, 0);
v_tail_340_ = lean_ctor_get(v_x_338_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_351_ == 0)
{
v___x_342_ = v_x_338_;
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_tail_340_);
lean_inc(v_head_339_);
lean_dec(v_x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
lean_inc(v_x_336_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 5);
lean_ctor_set(v___x_342_, 1, v_x_336_);
lean_ctor_set(v___x_342_, 0, v_x_337_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_x_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_x_336_);
v___x_345_ = v_reuseFailAlloc_350_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = l_String_quote(v_head_339_);
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_345_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v_x_337_ = v___x_348_;
v_x_338_ = v_tail_340_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_dec(v_x_352_);
return v_x_353_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_367_; 
v_head_355_ = lean_ctor_get(v_x_354_, 0);
v_tail_356_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_367_ == 0)
{
v___x_358_ = v_x_354_;
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_tail_356_);
lean_inc(v_head_355_);
lean_dec(v_x_354_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
lean_inc(v_x_352_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 5);
lean_ctor_set(v___x_358_, 1, v_x_352_);
lean_ctor_set(v___x_358_, 0, v_x_353_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_x_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_x_352_);
v___x_361_ = v_reuseFailAlloc_366_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = l_String_quote(v_head_355_);
v___x_363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(v_x_352_, v___x_364_, v_tail_356_);
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v___x_370_; 
lean_dec(v_x_369_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v_tail_371_; 
v_tail_371_ = lean_ctor_get(v_x_368_, 1);
if (lean_obj_tag(v_tail_371_) == 0)
{
lean_object* v_head_372_; lean_object* v___x_373_; 
lean_dec(v_x_369_);
v_head_372_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_head_372_);
lean_dec_ref_known(v_x_368_, 2);
v___x_373_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_372_);
return v___x_373_;
}
else
{
lean_object* v_head_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_inc(v_tail_371_);
v_head_374_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_head_374_);
lean_dec_ref_known(v_x_368_, 2);
v___x_375_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_374_);
v___x_376_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(v_x_369_, v___x_375_, v_tail_371_);
return v___x_376_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2));
v___x_389_ = lean_string_length(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7);
v___x_391_ = lean_nat_to_int(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(lean_object* v_a_396_){
_start:
{
if (lean_obj_tag(v_a_396_) == 0)
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1));
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_398_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5));
v___x_399_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(v_a_396_, v___x_398_);
v___x_400_ = lean_obj_once(&l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8);
v___x_401_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9));
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_399_);
v___x_403_ = ((lean_object*)(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10));
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_400_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Std_Format_fill(v___x_405_);
return v___x_406_;
}
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__8(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(2u);
v___x_420_ = lean_nat_to_int(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lake_instReprCliError_repr___closed__9(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_to_int(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr(lean_object* v_x_588_, lean_object* v_prec_589_){
_start:
{
lean_object* v___y_591_; lean_object* v___y_598_; lean_object* v___y_605_; lean_object* v___y_612_; 
switch(lean_obj_tag(v_x_588_))
{
case 0:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_589_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_605_ = v___x_620_;
goto v___jp_604_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_605_ = v___x_621_;
goto v___jp_604_;
}
}
case 1:
{
lean_object* v_cmd_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_642_; 
v_cmd_622_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_642_ == 0)
{
v___x_624_ = v_x_588_;
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_cmd_622_);
lean_dec(v_x_588_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___y_627_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_589_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_627_ = v___x_640_;
goto v___jp_626_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__12));
v___x_629_ = l_String_quote(v_cmd_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 3);
lean_ctor_set(v___x_624_, 0, v___x_629_);
v___x_631_ = v___x_624_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_628_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_inc(v___y_627_);
v___x_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_627_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = 0;
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_634_);
v___x_636_ = l_Repr_addAppParen(v___x_635_, v_prec_589_);
return v___x_636_;
}
}
}
}
case 2:
{
lean_object* v_arg_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_663_; 
v_arg_643_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_663_ == 0)
{
v___x_645_ = v_x_588_;
v_isShared_646_ = v_isSharedCheck_663_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_arg_643_);
lean_dec(v_x_588_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_663_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___y_648_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1024u);
v___x_660_ = lean_nat_dec_le(v___x_659_, v_prec_589_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_648_ = v___x_661_;
goto v___jp_647_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_648_ = v___x_662_;
goto v___jp_647_;
}
v___jp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__15));
v___x_650_ = l_String_quote(v_arg_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 3);
lean_ctor_set(v___x_645_, 0, v___x_650_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_658_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_649_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_inc(v___y_648_);
v___x_654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_654_, 0, v___y_648_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = 0;
v___x_656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_655_);
v___x_657_ = l_Repr_addAppParen(v___x_656_, v_prec_589_);
return v___x_657_;
}
}
}
}
case 3:
{
lean_object* v_opt_664_; lean_object* v_arg_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_690_; 
v_opt_664_ = lean_ctor_get(v_x_588_, 0);
v_arg_665_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_690_ == 0)
{
v___x_667_ = v_x_588_;
v_isShared_668_ = v_isSharedCheck_690_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_arg_665_);
lean_inc(v_opt_664_);
lean_dec(v_x_588_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_690_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___y_670_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(1024u);
v___x_687_ = lean_nat_dec_le(v___x_686_, v_prec_589_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_670_ = v___x_688_;
goto v___jp_669_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_670_ = v___x_689_;
goto v___jp_669_;
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_671_ = lean_box(1);
v___x_672_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__18));
v___x_673_ = l_String_quote(v_opt_664_);
v___x_674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 5);
lean_ctor_set(v___x_667_, 1, v___x_674_);
lean_ctor_set(v___x_667_, 0, v___x_672_);
v___x_676_ = v___x_667_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_685_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_671_);
v___x_678_ = l_String_quote(v_arg_665_);
v___x_679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_677_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
lean_inc(v___y_670_);
v___x_681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_670_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = 0;
v___x_683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_682_);
v___x_684_ = l_Repr_addAppParen(v___x_683_, v_prec_589_);
return v___x_684_;
}
}
}
}
case 4:
{
lean_object* v_opt_691_; lean_object* v_arg_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_717_; 
v_opt_691_ = lean_ctor_get(v_x_588_, 0);
v_arg_692_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_717_ == 0)
{
v___x_694_ = v_x_588_;
v_isShared_695_ = v_isSharedCheck_717_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_arg_692_);
lean_inc(v_opt_691_);
lean_dec(v_x_588_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_717_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___y_697_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(1024u);
v___x_714_ = lean_nat_dec_le(v___x_713_, v_prec_589_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_697_ = v___x_715_;
goto v___jp_696_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_697_ = v___x_716_;
goto v___jp_696_;
}
v___jp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_698_ = lean_box(1);
v___x_699_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__21));
v___x_700_ = l_String_quote(v_opt_691_);
v___x_701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 5);
lean_ctor_set(v___x_694_, 1, v___x_701_);
lean_ctor_set(v___x_694_, 0, v___x_699_);
v___x_703_ = v___x_694_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_712_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_698_);
v___x_705_ = l_String_quote(v_arg_692_);
v___x_706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
lean_inc(v___y_697_);
v___x_708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_708_, 0, v___y_697_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = 0;
v___x_710_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*1, v___x_709_);
v___x_711_ = l_Repr_addAppParen(v___x_710_, v_prec_589_);
return v___x_711_;
}
}
}
}
case 5:
{
uint32_t v_opt_718_; lean_object* v___y_720_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_opt_718_ = lean_ctor_get_uint32(v_x_588_, 0);
lean_dec_ref_known(v_x_588_, 0);
v___x_729_ = lean_unsigned_to_nat(1024u);
v___x_730_ = lean_nat_dec_le(v___x_729_, v_prec_589_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_720_ = v___x_731_;
goto v___jp_719_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_720_ = v___x_732_;
goto v___jp_719_;
}
v___jp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_721_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__24));
v___x_722_ = l_Char_quote(v_opt_718_);
v___x_723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
lean_inc(v___y_720_);
v___x_725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_725_, 0, v___y_720_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = 0;
v___x_727_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*1, v___x_726_);
v___x_728_ = l_Repr_addAppParen(v___x_727_, v_prec_589_);
return v___x_728_;
}
}
case 6:
{
lean_object* v_opt_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_753_; 
v_opt_733_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_753_ == 0)
{
v___x_735_ = v_x_588_;
v_isShared_736_ = v_isSharedCheck_753_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_opt_733_);
lean_dec(v_x_588_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_753_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___y_738_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(1024u);
v___x_750_ = lean_nat_dec_le(v___x_749_, v_prec_589_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_738_ = v___x_751_;
goto v___jp_737_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_738_ = v___x_752_;
goto v___jp_737_;
}
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_739_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__27));
v___x_740_ = l_String_quote(v_opt_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 3);
lean_ctor_set(v___x_735_, 0, v___x_740_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_748_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_739_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc(v___y_738_);
v___x_744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_744_, 0, v___y_738_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = 0;
v___x_746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_745_);
v___x_747_ = l_Repr_addAppParen(v___x_746_, v_prec_589_);
return v___x_747_;
}
}
}
}
case 7:
{
lean_object* v_args_754_; lean_object* v___y_756_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_args_754_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_args_754_);
lean_dec_ref_known(v_x_588_, 1);
v___x_764_ = lean_unsigned_to_nat(1024u);
v___x_765_ = lean_nat_dec_le(v___x_764_, v_prec_589_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_756_ = v___x_766_;
goto v___jp_755_;
}
else
{
lean_object* v___x_767_; 
v___x_767_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_756_ = v___x_767_;
goto v___jp_755_;
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__30));
v___x_758_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(v_args_754_);
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_inc(v___y_756_);
v___x_760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_760_, 0, v___y_756_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = 0;
v___x_762_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*1, v___x_761_);
v___x_763_ = l_Repr_addAppParen(v___x_762_, v_prec_589_);
return v___x_763_;
}
}
case 8:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(1024u);
v___x_769_ = lean_nat_dec_le(v___x_768_, v_prec_589_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_612_ = v___x_770_;
goto v___jp_611_;
}
else
{
lean_object* v___x_771_; 
v___x_771_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_612_ = v___x_771_;
goto v___jp_611_;
}
}
case 9:
{
lean_object* v_spec_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_792_; 
v_spec_772_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_792_ == 0)
{
v___x_774_ = v_x_588_;
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_spec_772_);
lean_dec(v_x_588_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___y_777_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(1024u);
v___x_789_ = lean_nat_dec_le(v___x_788_, v_prec_589_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_777_ = v___x_791_;
goto v___jp_776_;
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__33));
v___x_779_ = l_String_quote(v_spec_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 3);
lean_ctor_set(v___x_774_, 0, v___x_779_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_787_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_778_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_inc(v___y_777_);
v___x_783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_783_, 0, v___y_777_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = 0;
v___x_785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = l_Repr_addAppParen(v___x_785_, v_prec_589_);
return v___x_786_;
}
}
}
}
case 10:
{
lean_object* v_spec_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_813_; 
v_spec_793_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_813_ == 0)
{
v___x_795_ = v_x_588_;
v_isShared_796_ = v_isSharedCheck_813_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_spec_793_);
lean_dec(v_x_588_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_813_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___y_798_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(1024u);
v___x_810_ = lean_nat_dec_le(v___x_809_, v_prec_589_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_798_ = v___x_811_;
goto v___jp_797_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_798_ = v___x_812_;
goto v___jp_797_;
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__36));
v___x_800_ = l_String_quote(v_spec_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 3);
lean_ctor_set(v___x_795_, 0, v___x_800_);
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_808_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_799_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_inc(v___y_798_);
v___x_804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_804_, 0, v___y_798_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = 0;
v___x_806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_805_);
v___x_807_ = l_Repr_addAppParen(v___x_806_, v_prec_589_);
return v___x_807_;
}
}
}
}
case 11:
{
lean_object* v_mod_814_; lean_object* v___y_816_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_mod_814_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_mod_814_);
lean_dec_ref_known(v_x_588_, 1);
v___x_825_ = lean_unsigned_to_nat(1024u);
v___x_826_ = lean_nat_dec_le(v___x_825_, v_prec_589_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_816_ = v___x_827_;
goto v___jp_815_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_816_ = v___x_828_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_817_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__39));
v___x_818_ = lean_unsigned_to_nat(1024u);
v___x_819_ = l_Lean_Name_reprPrec(v_mod_814_, v___x_818_);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_817_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_inc(v___y_816_);
v___x_821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_816_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = 0;
v___x_823_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_822_);
v___x_824_ = l_Repr_addAppParen(v___x_823_, v_prec_589_);
return v___x_824_;
}
}
case 12:
{
lean_object* v_path_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_853_; 
v_path_829_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_853_ == 0)
{
v___x_831_ = v_x_588_;
v_isShared_832_ = v_isSharedCheck_853_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_path_829_);
lean_dec(v_x_588_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_853_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___y_834_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(1024u);
v___x_850_ = lean_nat_dec_le(v___x_849_, v_prec_589_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_834_ = v___x_851_;
goto v___jp_833_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_834_ = v___x_852_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_835_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__42));
v___x_836_ = lean_unsigned_to_nat(1024u);
v___x_837_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_838_ = l_String_quote(v_path_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 3);
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_848_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_837_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Repr_addAppParen(v___x_841_, v___x_836_);
v___x_843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_835_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_inc(v___y_834_);
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_834_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = 0;
v___x_846_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_845_);
v___x_847_ = l_Repr_addAppParen(v___x_846_, v_prec_589_);
return v___x_847_;
}
}
}
}
case 13:
{
lean_object* v_spec_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_spec_854_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_874_ == 0)
{
v___x_856_ = v_x_588_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_spec_854_);
lean_dec(v_x_588_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___y_859_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1024u);
v___x_871_ = lean_nat_dec_le(v___x_870_, v_prec_589_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_859_ = v___x_872_;
goto v___jp_858_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_859_ = v___x_873_;
goto v___jp_858_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__47));
v___x_861_ = l_String_quote(v_spec_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 3);
lean_ctor_set(v___x_856_, 0, v___x_861_);
v___x_863_ = v___x_856_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_869_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_860_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
lean_inc(v___y_859_);
v___x_865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_859_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = 0;
v___x_867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*1, v___x_866_);
v___x_868_ = l_Repr_addAppParen(v___x_867_, v_prec_589_);
return v___x_868_;
}
}
}
}
case 14:
{
lean_object* v_type_875_; lean_object* v_facet_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_901_; 
v_type_875_ = lean_ctor_get(v_x_588_, 0);
v_facet_876_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_901_ == 0)
{
v___x_878_ = v_x_588_;
v_isShared_879_ = v_isSharedCheck_901_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_facet_876_);
lean_inc(v_type_875_);
lean_dec(v_x_588_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_901_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___y_881_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = lean_unsigned_to_nat(1024u);
v___x_898_ = lean_nat_dec_le(v___x_897_, v_prec_589_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_881_ = v___x_899_;
goto v___jp_880_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_881_ = v___x_900_;
goto v___jp_880_;
}
v___jp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_882_ = lean_box(1);
v___x_883_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__50));
v___x_884_ = l_String_quote(v_type_875_);
v___x_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 5);
lean_ctor_set(v___x_878_, 1, v___x_885_);
lean_ctor_set(v___x_878_, 0, v___x_883_);
v___x_887_ = v___x_878_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_896_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_882_);
v___x_889_ = lean_unsigned_to_nat(1024u);
v___x_890_ = l_Lean_Name_reprPrec(v_facet_876_, v___x_889_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_888_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
lean_inc(v___y_881_);
v___x_892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_892_, 0, v___y_881_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = 0;
v___x_894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_893_);
v___x_895_ = l_Repr_addAppParen(v___x_894_, v_prec_589_);
return v___x_895_;
}
}
}
}
case 15:
{
lean_object* v_target_902_; lean_object* v___y_904_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_target_902_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_target_902_);
lean_dec_ref_known(v_x_588_, 1);
v___x_913_ = lean_unsigned_to_nat(1024u);
v___x_914_ = lean_nat_dec_le(v___x_913_, v_prec_589_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_904_ = v___x_915_;
goto v___jp_903_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_904_ = v___x_916_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_905_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__53));
v___x_906_ = lean_unsigned_to_nat(1024u);
v___x_907_ = l_Lean_Name_reprPrec(v_target_902_, v___x_906_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
lean_inc(v___y_904_);
v___x_909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_909_, 0, v___y_904_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = 0;
v___x_911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_910_);
v___x_912_ = l_Repr_addAppParen(v___x_911_, v_prec_589_);
return v___x_912_;
}
}
case 16:
{
lean_object* v_pkg_917_; lean_object* v_mod_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_942_; 
v_pkg_917_ = lean_ctor_get(v_x_588_, 0);
v_mod_918_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_942_ == 0)
{
v___x_920_ = v_x_588_;
v_isShared_921_ = v_isSharedCheck_942_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_mod_918_);
lean_inc(v_pkg_917_);
lean_dec(v_x_588_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_942_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___y_923_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(1024u);
v___x_939_ = lean_nat_dec_le(v___x_938_, v_prec_589_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_923_ = v___x_940_;
goto v___jp_922_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_923_ = v___x_941_;
goto v___jp_922_;
}
v___jp_922_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_924_ = lean_box(1);
v___x_925_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__56));
v___x_926_ = lean_unsigned_to_nat(1024u);
v___x_927_ = l_Lean_Name_reprPrec(v_pkg_917_, v___x_926_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 5);
lean_ctor_set(v___x_920_, 1, v___x_927_);
lean_ctor_set(v___x_920_, 0, v___x_925_);
v___x_929_ = v___x_920_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_937_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_924_);
v___x_931_ = l_Lean_Name_reprPrec(v_mod_918_, v___x_926_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_inc(v___y_923_);
v___x_933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_933_, 0, v___y_923_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = 0;
v___x_935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_934_);
v___x_936_ = l_Repr_addAppParen(v___x_935_, v_prec_589_);
return v___x_936_;
}
}
}
}
case 17:
{
lean_object* v_pkg_943_; lean_object* v_spec_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_969_; 
v_pkg_943_ = lean_ctor_get(v_x_588_, 0);
v_spec_944_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_969_ == 0)
{
v___x_946_ = v_x_588_;
v_isShared_947_ = v_isSharedCheck_969_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_spec_944_);
lean_inc(v_pkg_943_);
lean_dec(v_x_588_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_969_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___y_949_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1024u);
v___x_966_ = lean_nat_dec_le(v___x_965_, v_prec_589_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_949_ = v___x_967_;
goto v___jp_948_;
}
else
{
lean_object* v___x_968_; 
v___x_968_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_949_ = v___x_968_;
goto v___jp_948_;
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_950_ = lean_box(1);
v___x_951_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__59));
v___x_952_ = lean_unsigned_to_nat(1024u);
v___x_953_ = l_Lean_Name_reprPrec(v_pkg_943_, v___x_952_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 5);
lean_ctor_set(v___x_946_, 1, v___x_953_);
lean_ctor_set(v___x_946_, 0, v___x_951_);
v___x_955_ = v___x_946_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_964_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_950_);
v___x_957_ = l_String_quote(v_spec_944_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_inc(v___y_949_);
v___x_960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_960_, 0, v___y_949_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = 0;
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_961_);
v___x_963_ = l_Repr_addAppParen(v___x_962_, v_prec_589_);
return v___x_963_;
}
}
}
}
case 18:
{
lean_object* v_key_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_990_; 
v_key_970_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_990_ == 0)
{
v___x_972_ = v_x_588_;
v_isShared_973_ = v_isSharedCheck_990_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_key_970_);
lean_dec(v_x_588_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_990_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___y_975_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(1024u);
v___x_987_ = lean_nat_dec_le(v___x_986_, v_prec_589_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_975_ = v___x_988_;
goto v___jp_974_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_975_ = v___x_989_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_976_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__62));
v___x_977_ = l_String_quote(v_key_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 0, v___x_977_);
v___x_979_ = v___x_972_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_985_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_976_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
lean_inc(v___y_975_);
v___x_981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_981_, 0, v___y_975_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = 0;
v___x_983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_982_);
v___x_984_ = l_Repr_addAppParen(v___x_983_, v_prec_589_);
return v___x_984_;
}
}
}
}
case 19:
{
lean_object* v_spec_991_; uint32_t v_tooMany_992_; lean_object* v___y_994_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_spec_991_ = lean_ctor_get(v_x_588_, 0);
lean_inc_ref(v_spec_991_);
v_tooMany_992_ = lean_ctor_get_uint32(v_x_588_, sizeof(void*)*1);
lean_dec_ref_known(v_x_588_, 1);
v___x_1008_ = lean_unsigned_to_nat(1024u);
v___x_1009_ = lean_nat_dec_le(v___x_1008_, v_prec_589_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_994_ = v___x_1010_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_994_ = v___x_1011_;
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_995_ = lean_box(1);
v___x_996_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__65));
v___x_997_ = l_String_quote(v_spec_991_);
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_995_);
v___x_1001_ = l_Char_quote(v_tooMany_992_);
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1000_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
lean_inc(v___y_994_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_994_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1005_);
v___x_1007_ = l_Repr_addAppParen(v___x_1006_, v_prec_589_);
return v___x_1007_;
}
}
case 20:
{
lean_object* v_target_1012_; lean_object* v_facet_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1037_; 
v_target_1012_ = lean_ctor_get(v_x_588_, 0);
v_facet_1013_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1015_ = v_x_588_;
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_facet_1013_);
lean_inc(v_target_1012_);
lean_dec(v_x_588_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___y_1018_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(1024u);
v___x_1034_ = lean_nat_dec_le(v___x_1033_, v_prec_589_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1018_ = v___x_1035_;
goto v___jp_1017_;
}
else
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1018_ = v___x_1036_;
goto v___jp_1017_;
}
v___jp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1019_ = lean_box(1);
v___x_1020_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__68));
v___x_1021_ = lean_unsigned_to_nat(1024u);
v___x_1022_ = l_Lean_Name_reprPrec(v_target_1012_, v___x_1021_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 5);
lean_ctor_set(v___x_1015_, 1, v___x_1022_);
lean_ctor_set(v___x_1015_, 0, v___x_1020_);
v___x_1024_ = v___x_1015_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1019_);
v___x_1026_ = l_Lean_Name_reprPrec(v_facet_1013_, v___x_1021_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
lean_inc(v___y_1018_);
v___x_1028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1018_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = 0;
v___x_1030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1029_);
v___x_1031_ = l_Repr_addAppParen(v___x_1030_, v_prec_589_);
return v___x_1031_;
}
}
}
}
case 21:
{
lean_object* v_spec_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1058_; 
v_spec_1038_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1040_ = v_x_588_;
v_isShared_1041_ = v_isSharedCheck_1058_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_spec_1038_);
lean_dec(v_x_588_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1058_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___y_1043_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_unsigned_to_nat(1024u);
v___x_1055_ = lean_nat_dec_le(v___x_1054_, v_prec_589_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1043_ = v___x_1057_;
goto v___jp_1042_;
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__71));
v___x_1045_ = l_String_quote(v_spec_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 3);
lean_ctor_set(v___x_1040_, 0, v___x_1045_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1044_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
lean_inc(v___y_1043_);
v___x_1049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___y_1043_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = 0;
v___x_1051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*1, v___x_1050_);
v___x_1052_ = l_Repr_addAppParen(v___x_1051_, v_prec_589_);
return v___x_1052_;
}
}
}
}
case 22:
{
lean_object* v_script_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1079_; 
v_script_1059_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1061_ = v_x_588_;
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_script_1059_);
lean_dec(v_x_588_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___y_1064_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(1024u);
v___x_1076_ = lean_nat_dec_le(v___x_1075_, v_prec_589_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1064_ = v___x_1077_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1064_ = v___x_1078_;
goto v___jp_1063_;
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__74));
v___x_1066_ = l_String_quote(v_script_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 3);
lean_ctor_set(v___x_1061_, 0, v___x_1066_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1065_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
lean_inc(v___y_1064_);
v___x_1070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___y_1064_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = 0;
v___x_1072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*1, v___x_1071_);
v___x_1073_ = l_Repr_addAppParen(v___x_1072_, v_prec_589_);
return v___x_1073_;
}
}
}
}
case 23:
{
lean_object* v_script_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1100_; 
v_script_1080_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1082_ = v_x_588_;
v_isShared_1083_ = v_isSharedCheck_1100_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_script_1080_);
lean_dec(v_x_588_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1100_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___y_1085_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_unsigned_to_nat(1024u);
v___x_1097_ = lean_nat_dec_le(v___x_1096_, v_prec_589_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1085_ = v___x_1098_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1085_ = v___x_1099_;
goto v___jp_1084_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1086_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__77));
v___x_1087_ = l_String_quote(v_script_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 3);
lean_ctor_set(v___x_1082_, 0, v___x_1087_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1086_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_inc(v___y_1085_);
v___x_1091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1085_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = 0;
v___x_1093_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*1, v___x_1092_);
v___x_1094_ = l_Repr_addAppParen(v___x_1093_, v_prec_589_);
return v___x_1094_;
}
}
}
}
case 24:
{
lean_object* v_spec_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1121_; 
v_spec_1101_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1103_ = v_x_588_;
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_spec_1101_);
lean_dec(v_x_588_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___y_1106_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(1024u);
v___x_1118_ = lean_nat_dec_le(v___x_1117_, v_prec_589_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1106_ = v___x_1119_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1106_ = v___x_1120_;
goto v___jp_1105_;
}
v___jp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__80));
v___x_1108_ = l_String_quote(v_spec_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 3);
lean_ctor_set(v___x_1103_, 0, v___x_1108_);
v___x_1110_ = v___x_1103_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1107_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_inc(v___y_1106_);
v___x_1112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = 0;
v___x_1114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*1, v___x_1113_);
v___x_1115_ = l_Repr_addAppParen(v___x_1114_, v_prec_589_);
return v___x_1115_;
}
}
}
}
case 25:
{
lean_object* v_path_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1146_; 
v_path_1122_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1124_ = v_x_588_;
v_isShared_1125_ = v_isSharedCheck_1146_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_path_1122_);
lean_dec(v_x_588_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1146_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___y_1127_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1024u);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v_prec_589_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1127_ = v___x_1144_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1127_ = v___x_1145_;
goto v___jp_1126_;
}
v___jp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1128_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__83));
v___x_1129_ = lean_unsigned_to_nat(1024u);
v___x_1130_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_1131_ = l_String_quote(v_path_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 3);
lean_ctor_set(v___x_1124_, 0, v___x_1131_);
v___x_1133_ = v___x_1124_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Repr_addAppParen(v___x_1134_, v___x_1129_);
v___x_1136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1128_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_inc(v___y_1127_);
v___x_1137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1127_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = 0;
v___x_1139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*1, v___x_1138_);
v___x_1140_ = l_Repr_addAppParen(v___x_1139_, v_prec_589_);
return v___x_1140_;
}
}
}
}
case 26:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(1024u);
v___x_1148_ = lean_nat_dec_le(v___x_1147_, v_prec_589_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_598_ = v___x_1149_;
goto v___jp_597_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_598_ = v___x_1150_;
goto v___jp_597_;
}
}
case 27:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(1024u);
v___x_1152_ = lean_nat_dec_le(v___x_1151_, v_prec_589_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_591_ = v___x_1153_;
goto v___jp_590_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_591_ = v___x_1154_;
goto v___jp_590_;
}
}
case 28:
{
lean_object* v_expected_1155_; lean_object* v_actual_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1181_; 
v_expected_1155_ = lean_ctor_get(v_x_588_, 0);
v_actual_1156_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1158_ = v_x_588_;
v_isShared_1159_ = v_isSharedCheck_1181_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_actual_1156_);
lean_inc(v_expected_1155_);
lean_dec(v_x_588_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1181_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___y_1161_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(1024u);
v___x_1178_ = lean_nat_dec_le(v___x_1177_, v_prec_589_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1161_ = v___x_1179_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1161_ = v___x_1180_;
goto v___jp_1160_;
}
v___jp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1162_ = lean_box(1);
v___x_1163_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__86));
v___x_1164_ = l_String_quote(v_expected_1155_);
v___x_1165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 5);
lean_ctor_set(v___x_1158_, 1, v___x_1165_);
lean_ctor_set(v___x_1158_, 0, v___x_1163_);
v___x_1167_ = v___x_1158_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1162_);
v___x_1169_ = l_String_quote(v_actual_1156_);
v___x_1170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1168_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
lean_inc(v___y_1161_);
v___x_1172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___y_1161_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = 0;
v___x_1174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1, v___x_1173_);
v___x_1175_ = l_Repr_addAppParen(v___x_1174_, v_prec_589_);
return v___x_1175_;
}
}
}
}
case 29:
{
lean_object* v_msg_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1202_; 
v_msg_1182_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1184_ = v_x_588_;
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_msg_1182_);
lean_dec(v_x_588_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___y_1187_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = lean_unsigned_to_nat(1024u);
v___x_1199_ = lean_nat_dec_le(v___x_1198_, v_prec_589_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1187_ = v___x_1200_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1187_ = v___x_1201_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1188_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__89));
v___x_1189_ = l_String_quote(v_msg_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 3);
lean_ctor_set(v___x_1184_, 0, v___x_1189_);
v___x_1191_ = v___x_1184_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1188_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_inc(v___y_1187_);
v___x_1193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1187_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = 0;
v___x_1195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*1, v___x_1194_);
v___x_1196_ = l_Repr_addAppParen(v___x_1195_, v_prec_589_);
return v___x_1196_;
}
}
}
}
default: 
{
lean_object* v_path_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1227_; 
v_path_1203_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1205_ = v_x_588_;
v_isShared_1206_ = v_isSharedCheck_1227_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_path_1203_);
lean_dec(v_x_588_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1227_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___y_1208_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(1024u);
v___x_1224_ = lean_nat_dec_le(v___x_1223_, v_prec_589_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__8, &l_Lake_instReprCliError_repr___closed__8_once, _init_l_Lake_instReprCliError_repr___closed__8);
v___y_1208_ = v___x_1225_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_obj_once(&l_Lake_instReprCliError_repr___closed__9, &l_Lake_instReprCliError_repr___closed__9_once, _init_l_Lake_instReprCliError_repr___closed__9);
v___y_1208_ = v___x_1226_;
goto v___jp_1207_;
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__92));
v___x_1210_ = lean_unsigned_to_nat(1024u);
v___x_1211_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__44));
v___x_1212_ = l_String_quote(v_path_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 3);
lean_ctor_set(v___x_1205_, 0, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Repr_addAppParen(v___x_1215_, v___x_1210_);
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1209_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_inc(v___y_1208_);
v___x_1218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___y_1208_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = 0;
v___x_1220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*1, v___x_1219_);
v___x_1221_ = l_Repr_addAppParen(v___x_1220_, v_prec_589_);
return v___x_1221_;
}
}
}
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_592_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__1));
lean_inc(v___y_591_);
v___x_593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_593_, 0, v___y_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = 0;
v___x_595_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*1, v___x_594_);
v___x_596_ = l_Repr_addAppParen(v___x_595_, v_prec_589_);
return v___x_596_;
}
v___jp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_599_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__3));
lean_inc(v___y_598_);
v___x_600_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = 0;
v___x_602_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*1, v___x_601_);
v___x_603_ = l_Repr_addAppParen(v___x_602_, v_prec_589_);
return v___x_603_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_606_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__5));
lean_inc(v___y_605_);
v___x_607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_607_, 0, v___y_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = 0;
v___x_609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_608_);
v___x_610_ = l_Repr_addAppParen(v___x_609_, v_prec_589_);
return v___x_610_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_613_ = ((lean_object*)(l_Lake_instReprCliError_repr___closed__7));
lean_inc(v___y_612_);
v___x_614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_614_, 0, v___y_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = 0;
v___x_616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*1, v___x_615_);
v___x_617_ = l_Repr_addAppParen(v___x_616_, v_prec_589_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprCliError_repr___boxed(lean_object* v_x_1228_, lean_object* v_prec_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lake_instReprCliError_repr(v_x_1228_, v_prec_1229_);
lean_dec(v_prec_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__1(lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_nat_to_int(v_a_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(lean_object* v_a_1233_, lean_object* v_n_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(v_a_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___boxed(lean_object* v_a_1236_, lean_object* v_n_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(v_a_1236_, v_n_1237_);
lean_dec(v_n_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object* v_x_1285_){
_start:
{
switch(lean_obj_tag(v_x_1285_))
{
case 0:
{
lean_object* v___x_1286_; 
v___x_1286_ = ((lean_object*)(l_Lake_CliError_toString___closed__0));
return v___x_1286_;
}
case 1:
{
lean_object* v_cmd_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_cmd_1287_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_cmd_1287_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1288_ = ((lean_object*)(l_Lake_CliError_toString___closed__1));
v___x_1289_ = lean_string_append(v___x_1288_, v_cmd_1287_);
lean_dec_ref(v_cmd_1287_);
v___x_1290_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
return v___x_1291_;
}
case 2:
{
lean_object* v_arg_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_arg_1292_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_arg_1292_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1293_ = ((lean_object*)(l_Lake_CliError_toString___closed__3));
v___x_1294_ = lean_string_append(v___x_1293_, v_arg_1292_);
lean_dec_ref(v_arg_1292_);
return v___x_1294_;
}
case 3:
{
lean_object* v_opt_1295_; lean_object* v_arg_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_opt_1295_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_opt_1295_);
v_arg_1296_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_arg_1296_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1297_ = ((lean_object*)(l_Lake_CliError_toString___closed__3));
v___x_1298_ = lean_string_append(v___x_1297_, v_arg_1296_);
lean_dec_ref(v_arg_1296_);
v___x_1299_ = ((lean_object*)(l_Lake_CliError_toString___closed__4));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_string_append(v___x_1300_, v_opt_1295_);
lean_dec_ref(v_opt_1295_);
return v___x_1301_;
}
case 4:
{
lean_object* v_opt_1302_; lean_object* v_arg_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_opt_1302_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_opt_1302_);
v_arg_1303_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_arg_1303_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1304_ = ((lean_object*)(l_Lake_CliError_toString___closed__5));
v___x_1305_ = lean_string_append(v___x_1304_, v_opt_1302_);
lean_dec_ref(v_opt_1302_);
v___x_1306_ = ((lean_object*)(l_Lake_CliError_toString___closed__6));
v___x_1307_ = lean_string_append(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_string_append(v___x_1307_, v_arg_1303_);
lean_dec_ref(v_arg_1303_);
return v___x_1308_;
}
case 5:
{
uint32_t v_opt_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_opt_1309_ = lean_ctor_get_uint32(v_x_1285_, 0);
lean_dec_ref_known(v_x_1285_, 0);
v___x_1310_ = ((lean_object*)(l_Lake_CliError_toString___closed__7));
v___x_1311_ = ((lean_object*)(l_Lake_CliError_toString___closed__8));
v___x_1312_ = lean_string_push(v___x_1311_, v_opt_1309_);
v___x_1313_ = lean_string_append(v___x_1310_, v___x_1312_);
lean_dec_ref(v___x_1312_);
v___x_1314_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1315_ = lean_string_append(v___x_1313_, v___x_1314_);
return v___x_1315_;
}
case 6:
{
lean_object* v_opt_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_opt_1316_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_opt_1316_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1317_ = ((lean_object*)(l_Lake_CliError_toString___closed__9));
v___x_1318_ = lean_string_append(v___x_1317_, v_opt_1316_);
lean_dec_ref(v_opt_1316_);
v___x_1319_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
return v___x_1320_;
}
case 7:
{
lean_object* v_args_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_args_1321_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_args_1321_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1322_ = ((lean_object*)(l_Lake_CliError_toString___closed__10));
v___x_1323_ = ((lean_object*)(l_Lake_CliError_toString___closed__11));
v___x_1324_ = l_String_intercalate(v___x_1323_, v_args_1321_);
v___x_1325_ = lean_string_append(v___x_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
return v___x_1325_;
}
case 8:
{
lean_object* v___x_1326_; 
v___x_1326_ = ((lean_object*)(l_Lake_CliError_toString___closed__12));
return v___x_1326_;
}
case 9:
{
lean_object* v_spec_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_spec_1327_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1327_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1328_ = ((lean_object*)(l_Lake_CliError_toString___closed__13));
v___x_1329_ = lean_string_append(v___x_1328_, v_spec_1327_);
lean_dec_ref(v_spec_1327_);
v___x_1330_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
return v___x_1331_;
}
case 10:
{
lean_object* v_spec_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_spec_1332_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1332_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1333_ = ((lean_object*)(l_Lake_CliError_toString___closed__15));
v___x_1334_ = lean_string_append(v___x_1333_, v_spec_1332_);
lean_dec_ref(v_spec_1332_);
v___x_1335_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1336_ = lean_string_append(v___x_1334_, v___x_1335_);
return v___x_1336_;
}
case 11:
{
lean_object* v_mod_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_mod_1337_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_mod_1337_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1338_ = ((lean_object*)(l_Lake_CliError_toString___closed__16));
v___x_1339_ = 0;
v___x_1340_ = l_Lean_Name_toString(v_mod_1337_, v___x_1339_);
v___x_1341_ = lean_string_append(v___x_1338_, v___x_1340_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1343_ = lean_string_append(v___x_1341_, v___x_1342_);
return v___x_1343_;
}
case 12:
{
lean_object* v_path_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_path_1344_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_path_1344_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1345_ = ((lean_object*)(l_Lake_CliError_toString___closed__17));
v___x_1346_ = lean_string_append(v___x_1345_, v_path_1344_);
lean_dec_ref(v_path_1344_);
v___x_1347_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
return v___x_1348_;
}
case 13:
{
lean_object* v_spec_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_spec_1349_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1349_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1350_ = ((lean_object*)(l_Lake_CliError_toString___closed__18));
v___x_1351_ = lean_string_append(v___x_1350_, v_spec_1349_);
lean_dec_ref(v_spec_1349_);
v___x_1352_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
return v___x_1353_;
}
case 14:
{
lean_object* v_type_1354_; lean_object* v_facet_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_type_1354_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_type_1354_);
v_facet_1355_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_facet_1355_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1356_ = ((lean_object*)(l_Lake_CliError_toString___closed__19));
v___x_1357_ = lean_string_append(v___x_1356_, v_type_1354_);
lean_dec_ref(v_type_1354_);
v___x_1358_ = ((lean_object*)(l_Lake_CliError_toString___closed__20));
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
v___x_1360_ = 0;
v___x_1361_ = l_Lean_Name_toString(v_facet_1355_, v___x_1360_);
v___x_1362_ = lean_string_append(v___x_1359_, v___x_1361_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
return v___x_1364_;
}
case 15:
{
lean_object* v_target_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_target_1365_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_target_1365_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1366_ = ((lean_object*)(l_Lake_CliError_toString___closed__21));
v___x_1367_ = 0;
v___x_1368_ = l_Lean_Name_toString(v_target_1365_, v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
return v___x_1371_;
}
case 16:
{
lean_object* v_pkg_1372_; lean_object* v_mod_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_pkg_1372_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_pkg_1372_);
v_mod_1373_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_mod_1373_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1374_ = ((lean_object*)(l_Lake_CliError_toString___closed__22));
v___x_1375_ = 0;
v___x_1376_ = l_Lean_Name_toString(v_pkg_1372_, v___x_1375_);
v___x_1377_ = lean_string_append(v___x_1374_, v___x_1376_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Lake_CliError_toString___closed__23));
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_Name_toString(v_mod_1373_, v___x_1375_);
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
return v___x_1383_;
}
case 17:
{
lean_object* v_pkg_1384_; lean_object* v_spec_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_pkg_1384_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_pkg_1384_);
v_spec_1385_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_spec_1385_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1386_ = ((lean_object*)(l_Lake_CliError_toString___closed__22));
v___x_1387_ = 0;
v___x_1388_ = l_Lean_Name_toString(v_pkg_1384_, v___x_1387_);
v___x_1389_ = lean_string_append(v___x_1386_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lake_CliError_toString___closed__24));
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
v___x_1392_ = lean_string_append(v___x_1391_, v_spec_1385_);
lean_dec_ref(v_spec_1385_);
v___x_1393_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
return v___x_1394_;
}
case 18:
{
lean_object* v_key_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_key_1395_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_key_1395_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1396_ = ((lean_object*)(l_Lake_CliError_toString___closed__2));
v___x_1397_ = lean_string_append(v___x_1396_, v_key_1395_);
lean_dec_ref(v_key_1395_);
v___x_1398_ = ((lean_object*)(l_Lake_CliError_toString___closed__25));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
return v___x_1399_;
}
case 19:
{
lean_object* v_spec_1400_; uint32_t v_tooMany_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_spec_1400_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1400_);
v_tooMany_1401_ = lean_ctor_get_uint32(v_x_1285_, sizeof(void*)*1);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1402_ = ((lean_object*)(l_Lake_CliError_toString___closed__26));
v___x_1403_ = lean_string_append(v___x_1402_, v_spec_1400_);
lean_dec_ref(v_spec_1400_);
v___x_1404_ = ((lean_object*)(l_Lake_CliError_toString___closed__27));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lake_CliError_toString___closed__8));
v___x_1407_ = lean_string_push(v___x_1406_, v_tooMany_1401_);
v___x_1408_ = lean_string_append(v___x_1405_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = ((lean_object*)(l_Lake_CliError_toString___closed__28));
v___x_1410_ = lean_string_append(v___x_1408_, v___x_1409_);
return v___x_1410_;
}
case 20:
{
lean_object* v_target_1411_; lean_object* v_facet_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_target_1411_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_target_1411_);
v_facet_1412_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_facet_1412_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1413_ = ((lean_object*)(l_Lake_CliError_toString___closed__29));
v___x_1414_ = 0;
v___x_1415_ = l_Lean_Name_toString(v_facet_1412_, v___x_1414_);
v___x_1416_ = lean_string_append(v___x_1413_, v___x_1415_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lake_CliError_toString___closed__30));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = l_Lean_Name_toString(v_target_1411_, v___x_1414_);
v___x_1420_ = lean_string_append(v___x_1418_, v___x_1419_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = ((lean_object*)(l_Lake_CliError_toString___closed__31));
v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
return v___x_1422_;
}
case 21:
{
lean_object* v_spec_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_spec_1423_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1423_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1424_ = ((lean_object*)(l_Lake_CliError_toString___closed__32));
v___x_1425_ = lean_string_append(v___x_1424_, v_spec_1423_);
lean_dec_ref(v_spec_1423_);
return v___x_1425_;
}
case 22:
{
lean_object* v_script_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_script_1426_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_script_1426_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1427_ = ((lean_object*)(l_Lake_CliError_toString___closed__33));
v___x_1428_ = lean_string_append(v___x_1427_, v_script_1426_);
lean_dec_ref(v_script_1426_);
return v___x_1428_;
}
case 23:
{
lean_object* v_script_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_script_1429_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_script_1429_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1430_ = ((lean_object*)(l_Lake_CliError_toString___closed__34));
v___x_1431_ = lean_string_append(v___x_1430_, v_script_1429_);
lean_dec_ref(v_script_1429_);
v___x_1432_ = ((lean_object*)(l_Lake_CliError_toString___closed__14));
v___x_1433_ = lean_string_append(v___x_1431_, v___x_1432_);
return v___x_1433_;
}
case 24:
{
lean_object* v_spec_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_spec_1434_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_spec_1434_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1435_ = ((lean_object*)(l_Lake_CliError_toString___closed__35));
v___x_1436_ = lean_string_append(v___x_1435_, v_spec_1434_);
lean_dec_ref(v_spec_1434_);
v___x_1437_ = ((lean_object*)(l_Lake_CliError_toString___closed__36));
v___x_1438_ = lean_string_append(v___x_1436_, v___x_1437_);
return v___x_1438_;
}
case 25:
{
lean_object* v_path_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_path_1439_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_path_1439_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1440_ = ((lean_object*)(l_Lake_CliError_toString___closed__37));
v___x_1441_ = lean_string_append(v___x_1440_, v_path_1439_);
lean_dec_ref(v_path_1439_);
return v___x_1441_;
}
case 26:
{
lean_object* v___x_1442_; 
v___x_1442_ = ((lean_object*)(l_Lake_CliError_toString___closed__38));
return v___x_1442_;
}
case 27:
{
lean_object* v___x_1443_; 
v___x_1443_ = ((lean_object*)(l_Lake_CliError_toString___closed__39));
return v___x_1443_;
}
case 28:
{
lean_object* v_expected_1444_; lean_object* v_actual_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_expected_1444_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_expected_1444_);
v_actual_1445_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_actual_1445_);
lean_dec_ref_known(v_x_1285_, 2);
v___x_1446_ = ((lean_object*)(l_Lake_CliError_toString___closed__40));
v___x_1447_ = lean_string_append(v___x_1446_, v_expected_1444_);
lean_dec_ref(v_expected_1444_);
v___x_1448_ = ((lean_object*)(l_Lake_CliError_toString___closed__41));
v___x_1449_ = lean_string_append(v___x_1447_, v___x_1448_);
v___x_1450_ = lean_string_utf8_byte_size(v_actual_1445_);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_nat_dec_eq(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_string_append(v___x_1449_, v_actual_1445_);
lean_dec_ref(v_actual_1445_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_actual_1445_);
v___x_1454_ = ((lean_object*)(l_Lake_CliError_toString___closed__42));
v___x_1455_ = lean_string_append(v___x_1449_, v___x_1454_);
return v___x_1455_;
}
}
case 29:
{
lean_object* v_msg_1456_; 
v_msg_1456_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_msg_1456_);
lean_dec_ref_known(v_x_1285_, 1);
return v_msg_1456_;
}
default: 
{
lean_object* v_path_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_path_1457_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_path_1457_);
lean_dec_ref_known(v_x_1285_, 1);
v___x_1458_ = ((lean_object*)(l_Lake_CliError_toString___closed__43));
v___x_1459_ = lean_string_append(v___x_1458_, v_path_1457_);
lean_dec_ref(v_path_1457_);
return v___x_1459_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: public import Lean.Compiler.FFI public import Lake.Config.Dynlib public import Lake.Config.Defaults public import Lake.Util.NativeLib import Init.Data.String.Modify import Init.System.Platform
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
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedDynlib_default;
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_app_path();
lean_object* l_System_FilePath_parent(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_Lake_sharedLibExt;
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBuildDir;
extern lean_object* l_Lake_defaultBinDir;
extern lean_object* l_Lake_defaultLeanLibDir;
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_envToBool_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l_Lake_envToBool_x3f___closed__0 = (const lean_object*)&l_Lake_envToBool_x3f___closed__0_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "yes"};
static const lean_object* l_Lake_envToBool_x3f___closed__1 = (const lean_object*)&l_Lake_envToBool_x3f___closed__1_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lake_envToBool_x3f___closed__2 = (const lean_object*)&l_Lake_envToBool_x3f___closed__2_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_envToBool_x3f___closed__3 = (const lean_object*)&l_Lake_envToBool_x3f___closed__3_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "on"};
static const lean_object* l_Lake_envToBool_x3f___closed__4 = (const lean_object*)&l_Lake_envToBool_x3f___closed__4_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Lake_envToBool_x3f___closed__5 = (const lean_object*)&l_Lake_envToBool_x3f___closed__5_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_envToBool_x3f___closed__6 = (const lean_object*)&l_Lake_envToBool_x3f___closed__6_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__4_value),((lean_object*)&l_Lake_envToBool_x3f___closed__6_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__7 = (const lean_object*)&l_Lake_envToBool_x3f___closed__7_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__3_value),((lean_object*)&l_Lake_envToBool_x3f___closed__7_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__8 = (const lean_object*)&l_Lake_envToBool_x3f___closed__8_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__2_value),((lean_object*)&l_Lake_envToBool_x3f___closed__8_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__9 = (const lean_object*)&l_Lake_envToBool_x3f___closed__9_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__1_value),((lean_object*)&l_Lake_envToBool_x3f___closed__9_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__10 = (const lean_object*)&l_Lake_envToBool_x3f___closed__10_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__0_value),((lean_object*)&l_Lake_envToBool_x3f___closed__10_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__11 = (const lean_object*)&l_Lake_envToBool_x3f___closed__11_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Lake_envToBool_x3f___closed__12 = (const lean_object*)&l_Lake_envToBool_x3f___closed__12_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "no"};
static const lean_object* l_Lake_envToBool_x3f___closed__13 = (const lean_object*)&l_Lake_envToBool_x3f___closed__13_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lake_envToBool_x3f___closed__14 = (const lean_object*)&l_Lake_envToBool_x3f___closed__14_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_envToBool_x3f___closed__15 = (const lean_object*)&l_Lake_envToBool_x3f___closed__15_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* l_Lake_envToBool_x3f___closed__16 = (const lean_object*)&l_Lake_envToBool_x3f___closed__16_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lake_envToBool_x3f___closed__17 = (const lean_object*)&l_Lake_envToBool_x3f___closed__17_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_envToBool_x3f___closed__18 = (const lean_object*)&l_Lake_envToBool_x3f___closed__18_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__16_value),((lean_object*)&l_Lake_envToBool_x3f___closed__18_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__19 = (const lean_object*)&l_Lake_envToBool_x3f___closed__19_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__15_value),((lean_object*)&l_Lake_envToBool_x3f___closed__19_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__20 = (const lean_object*)&l_Lake_envToBool_x3f___closed__20_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__14_value),((lean_object*)&l_Lake_envToBool_x3f___closed__20_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__21 = (const lean_object*)&l_Lake_envToBool_x3f___closed__21_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__13_value),((lean_object*)&l_Lake_envToBool_x3f___closed__21_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__22 = (const lean_object*)&l_Lake_envToBool_x3f___closed__22_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__12_value),((lean_object*)&l_Lake_envToBool_x3f___closed__22_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__23 = (const lean_object*)&l_Lake_envToBool_x3f___closed__23_value;
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object*);
static const lean_string_object l_Lake_instInhabitedElanInstall_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedElanInstall_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedElanInstall_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedElanInstall_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedElanInstall_default = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedElanInstall = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "home"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elan"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__16;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toolchainsDir"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__17_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__19;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__21;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__22;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__20_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprElanInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprElanInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprElanInstall___closed__0 = (const lean_object*)&l_Lake_instReprElanInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprElanInstall = (const lean_object*)&l_Lake_instReprElanInstall___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "---"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_leanExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lake_leanExe___closed__0 = (const lean_object*)&l_Lake_leanExe___closed__0_value;
static const lean_string_object l_Lake_leanExe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_leanExe___closed__1 = (const lean_object*)&l_Lake_leanExe___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object*);
static const lean_string_object l_Lake_leanirExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "leanir"};
static const lean_object* l_Lake_leanirExe___closed__0 = (const lean_object*)&l_Lake_leanirExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object*);
static const lean_string_object l_Lake_leancExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "leanc"};
static const lean_object* l_Lake_leancExe___closed__0 = (const lean_object*)&l_Lake_leancExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object*);
static const lean_string_object l_Lake_leantarExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leantar"};
static const lean_object* l_Lake_leantarExe___closed__0 = (const lean_object*)&l_Lake_leantarExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object*);
static const lean_string_object l_Lake_leanArExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "llvm-ar"};
static const lean_object* l_Lake_leanArExe___closed__0 = (const lean_object*)&l_Lake_leanArExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object*);
static const lean_string_object l_Lake_leanCcExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clang"};
static const lean_object* l_Lake_leanCcExe___closed__0 = (const lean_object*)&l_Lake_leanCcExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object*);
static const lean_string_object l_Lake_leanSharedLibDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_leanSharedLibDir___closed__0 = (const lean_object*)&l_Lake_leanSharedLibDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object*);
static const lean_string_object l_Lake_leanSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "libleanshared"};
static const lean_object* l_Lake_leanSharedLib___closed__0 = (const lean_object*)&l_Lake_leanSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_leanSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedLib___closed__1;
LEAN_EXPORT lean_object* l_Lake_leanSharedLib;
static const lean_string_object l_Lake_initSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "libInit_shared"};
static const lean_object* l_Lake_initSharedLib___closed__0 = (const lean_object*)&l_Lake_initSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_initSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initSharedLib___closed__1;
LEAN_EXPORT lean_object* l_Lake_initSharedLib;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ar"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cc"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__1_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-Wno-unused-command-line-argument"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__2_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__3;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__4;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__5;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__6;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sysroot"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "githash"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__6_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__7 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__8_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__11;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "includeDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "systemLibDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__16;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanExe___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanirExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leancExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__20;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leantarExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__21_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__22 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__24;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initSharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__26 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__27_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "customCc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__31_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ccFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__43_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__46 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__46_value;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLeanInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLeanInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLeanInstall___closed__0 = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLeanInstall = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_lakeExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l_Lake_lakeExe___closed__0 = (const lean_object*)&l_Lake_lakeExe___closed__0_value;
static lean_once_cell_t l_Lake_lakeExe___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lakeExe___closed__1;
LEAN_EXPORT lean_object* l_Lake_lakeExe;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall;
static const lean_string_object l_Lake_instReprLakeInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "libDir"};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__1_value;
static const lean_string_object l_Lake_instReprLakeInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sharedDynlib"};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_lakeExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLakeInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLakeInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLakeInstall___closed__0 = (const lean_object*)&l_Lake_instReprLakeInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLakeInstall = (const lean_object*)&l_Lake_instReprLakeInstall___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object*);
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lake_shared"};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__0 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__0_value;
static const lean_array_object l_Lake_LakeInstall_ofLean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__1 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__1_value;
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libLake_shared."};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__2 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__2_value;
static lean_once_cell_t l_Lake_LakeInstall_ofLean___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeInstall_ofLean___closed__3;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object*);
static const lean_string_object l_Lake_findElanInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__0_value;
static const lean_string_object l_Lake_findElanInstall_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__1 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__1_value;
static const lean_string_object l_Lake_findElanInstall_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toolchains"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__2 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object*);
static const lean_ctor_object l_Lake_findLeanSysroot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__0 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__0_value;
static const lean_string_object l_Lake_findLeanSysroot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--print-prefix"};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__1 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__1_value;
static const lean_array_object l_Lake_findLeanSysroot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_findLeanSysroot_x3f___closed__1_value)}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__2 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__2_value;
static const lean_array_object l_Lake_findLeanSysroot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__3 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--githash"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value;
static const lean_array_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value)}};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_AR"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AR"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_CC"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "CC"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_LeanInstall_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lake_LeanInstall_get___closed__0 = (const lean_object*)&l_Lake_LeanInstall_get___closed__0_value;
static const lean_string_object l_Lake_LeanInstall_get___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lake_LeanInstall_get___closed__1 = (const lean_object*)&l_Lake_LeanInstall_get___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f();
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object*);
static const lean_string_object l_Lake_getLakeInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_getLakeInstall_x3f___closed__0 = (const lean_object*)&l_Lake_getLakeInstall_x3f___closed__0_value;
static lean_once_cell_t l_Lake_getLakeInstall_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_getLakeInstall_x3f___closed__1;
static const lean_string_object l_Lake_getLakeInstall_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lake.olean"};
static const lean_object* l_Lake_getLakeInstall_x3f___closed__2 = (const lean_object*)&l_Lake_getLakeInstall_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_findLeanInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lake_findLeanInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findLeanInstall_x3f___closed__0_value;
static const lean_string_object l_Lake_findLeanInstall_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LEAN"};
static const lean_object* l_Lake_findLeanInstall_x3f___closed__1 = (const lean_object*)&l_Lake_findLeanInstall_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_findLakeInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LAKE_HOME"};
static const lean_object* l_Lake_findLakeInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findLakeInstall_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_findInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_OVERRIDE_LEAN"};
static const lean_object* l_Lake_findInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findInstall_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v___x_6_ = lean_string_dec_eq(v_a_1_, v_head_4_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object* v_s_12_, lean_object* v_p_13_){
_start:
{
uint32_t v___y_15_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_string_utf8_byte_size(v_s_12_);
v___x_21_ = lean_nat_dec_eq(v_p_13_, v___x_20_);
if (v___x_21_ == 0)
{
uint32_t v___x_22_; uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_string_utf8_get_fast(v_s_12_, v_p_13_);
v___x_23_ = 65;
v___x_24_ = lean_uint32_dec_le(v___x_23_, v___x_22_);
if (v___x_24_ == 0)
{
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 90;
v___x_26_ = lean_uint32_dec_le(v___x_22_, v___x_25_);
if (v___x_26_ == 0)
{
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
uint32_t v___x_27_; uint32_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_add(v___x_22_, v___x_27_);
v___y_15_ = v___x_28_;
goto v___jp_14_;
}
}
}
else
{
lean_dec(v_p_13_);
return v_s_12_;
}
v___jp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc(v_p_13_);
v___x_16_ = lean_string_utf8_set(v_s_12_, v_p_13_, v___y_15_);
v___x_17_ = l_Char_utf8Size(v___y_15_);
v___x_18_ = lean_nat_add(v_p_13_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v_p_13_);
v_s_12_ = v___x_16_;
v_p_13_ = v___x_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* v_o_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_78_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__11));
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_77_, v___x_79_);
v___x_81_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_80_, v___x_78_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__23));
v___x_83_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_80_, v___x_82_);
lean_dec_ref(v___x_80_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(v___x_81_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v___x_80_);
v___x_87_ = lean_box(v___x_81_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_nat_to_int(v_a_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(8u);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(10u);
v___x_124_ = lean_nat_to_int(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(17u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_132_ = lean_string_length(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_139_){
_start:
{
lean_object* v_home_140_; lean_object* v_elan_141_; lean_object* v_binDir_142_; lean_object* v_toolchainsDir_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_home_140_ = lean_ctor_get(v_x_139_, 0);
lean_inc_ref(v_home_140_);
v_elan_141_ = lean_ctor_get(v_x_139_, 1);
lean_inc_ref(v_elan_141_);
v_binDir_142_ = lean_ctor_get(v_x_139_, 2);
lean_inc_ref(v_binDir_142_);
v_toolchainsDir_143_ = lean_ctor_get(v_x_139_, 3);
lean_inc_ref(v_toolchainsDir_143_);
lean_dec_ref(v_x_139_);
v___x_144_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_145_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_146_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_149_ = l_String_quote(v_home_140_);
v___x_150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_148_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Repr_addAppParen(v___x_151_, v___x_147_);
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_146_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_145_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_box(1);
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_144_);
v___x_164_ = l_String_quote(v_elan_141_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_148_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Repr_addAppParen(v___x_166_, v___x_147_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_146_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_154_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_163_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_157_);
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_159_);
v___x_173_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_144_);
v___x_176_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_177_ = l_String_quote(v_binDir_142_);
v___x_178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_148_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Repr_addAppParen(v___x_179_, v___x_147_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_176_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_154_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_175_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_157_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_159_);
v___x_186_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_144_);
v___x_189_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_190_ = l_String_quote(v_toolchainsDir_143_);
v___x_191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_148_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Repr_addAppParen(v___x_192_, v___x_147_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_189_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_154_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_188_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_198_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_196_);
v___x_200_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_197_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_154_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_204_, lean_object* v_prec_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lake_instReprElanInstall_repr___redArg(v_x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_207_, lean_object* v_prec_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_instReprElanInstall_repr(v_x_207_, v_prec_208_);
lean_dec(v_prec_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_214_, lean_object* v_acc_215_, lean_object* v_pos_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lean_string_utf8_at_end(v_toolchain_214_, v_pos_216_);
if (v___x_217_ == 0)
{
uint32_t v_c_218_; lean_object* v_pos_x27_219_; uint32_t v___x_220_; uint8_t v___x_221_; 
v_c_218_ = lean_string_utf8_get_fast(v_toolchain_214_, v_pos_216_);
v_pos_x27_219_ = lean_string_utf8_next_fast(v_toolchain_214_, v_pos_216_);
lean_dec(v_pos_216_);
v___x_220_ = 47;
v___x_221_ = lean_uint32_dec_eq(v_c_218_, v___x_220_);
if (v___x_221_ == 0)
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 58;
v___x_223_ = lean_uint32_dec_eq(v_c_218_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_string_push(v_acc_215_, v_c_218_);
v_acc_215_ = v___x_224_;
v_pos_216_ = v_pos_x27_219_;
goto _start;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_227_ = lean_string_append(v_acc_215_, v___x_226_);
v_acc_215_ = v___x_227_;
v_pos_216_ = v_pos_x27_219_;
goto _start;
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_230_ = lean_string_append(v_acc_215_, v___x_229_);
v_acc_215_ = v___x_230_;
v_pos_216_ = v_pos_x27_219_;
goto _start;
}
}
else
{
lean_dec(v_pos_216_);
return v_acc_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_232_, lean_object* v_acc_233_, lean_object* v_pos_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_232_, v_acc_233_, v_pos_234_);
lean_dec_ref(v_toolchain_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_toolchain2Dir(v_toolchain_240_);
lean_dec_ref(v_toolchain_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_242_, lean_object* v_elan_243_){
_start:
{
lean_object* v_toolchainsDir_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_toolchainsDir_244_ = lean_ctor_get(v_elan_243_, 3);
lean_inc_ref(v_toolchainsDir_244_);
lean_dec_ref(v_elan_243_);
v___x_245_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_242_, v___x_245_, v___x_246_);
v___x_248_ = l_System_FilePath_join(v_toolchainsDir_244_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_249_, lean_object* v_elan_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_249_, v_elan_250_);
lean_dec_ref(v_toolchain_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_256_ = l_System_FilePath_join(v_sysroot_254_, v___x_255_);
v___x_257_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_258_ = l_System_FilePath_join(v___x_256_, v___x_257_);
v___x_259_ = l_System_FilePath_exeExtension;
v___x_260_ = l_System_FilePath_addExtension(v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_264_ = l_System_FilePath_join(v_sysroot_262_, v___x_263_);
v___x_265_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_266_ = l_System_FilePath_join(v___x_264_, v___x_265_);
v___x_267_ = l_System_FilePath_exeExtension;
v___x_268_ = l_System_FilePath_addExtension(v___x_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_272_ = l_System_FilePath_join(v_sysroot_270_, v___x_271_);
v___x_273_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_274_ = l_System_FilePath_join(v___x_272_, v___x_273_);
v___x_275_ = l_System_FilePath_exeExtension;
v___x_276_ = l_System_FilePath_addExtension(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_280_ = l_System_FilePath_join(v_sysroot_278_, v___x_279_);
v___x_281_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_282_ = l_System_FilePath_join(v___x_280_, v___x_281_);
v___x_283_ = l_System_FilePath_exeExtension;
v___x_284_ = l_System_FilePath_addExtension(v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_288_ = l_System_FilePath_join(v_sysroot_286_, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_290_ = l_System_FilePath_join(v___x_288_, v___x_289_);
v___x_291_ = l_System_FilePath_exeExtension;
v___x_292_ = l_System_FilePath_addExtension(v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_296_ = l_System_FilePath_join(v_sysroot_294_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_298_ = l_System_FilePath_join(v___x_296_, v___x_297_);
v___x_299_ = l_System_FilePath_exeExtension;
v___x_300_ = l_System_FilePath_addExtension(v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_System_Platform_isWindows;
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_305_ = l_System_FilePath_join(v_sysroot_302_, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_307_ = l_System_FilePath_join(v___x_305_, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_309_ = l_System_FilePath_join(v_sysroot_302_, v___x_308_);
return v___x_309_;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lake_sharedLibExt;
v___x_312_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_313_ = l_System_FilePath_addExtension(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_314_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = l_Lake_sharedLibExt;
v___x_317_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_318_ = l_System_FilePath_addExtension(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__2));
v___x_324_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_325_ = lean_array_push(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; 
v___x_326_ = 1;
v___x_327_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__5(void){
_start:
{
uint8_t v___x_328_; lean_object* v___x_329_; 
v___x_328_ = 0;
v___x_329_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_330_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__5, &l_Lake_instInhabitedLeanInstall_default___closed__5_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__5);
v___x_331_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_332_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_333_ = 1;
v___x_334_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__1));
v___x_335_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_336_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_337_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
lean_ctor_set(v___x_337_, 5, v___x_336_);
lean_ctor_set(v___x_337_, 6, v___x_336_);
lean_ctor_set(v___x_337_, 7, v___x_336_);
lean_ctor_set(v___x_337_, 8, v___x_336_);
lean_ctor_set(v___x_337_, 9, v___x_336_);
lean_ctor_set(v___x_337_, 10, v___x_336_);
lean_ctor_set(v___x_337_, 11, v___x_336_);
lean_ctor_set(v___x_337_, 12, v___x_336_);
lean_ctor_set(v___x_337_, 13, v___x_335_);
lean_ctor_set(v___x_337_, 14, v___x_334_);
lean_ctor_set(v___x_337_, 15, v___x_332_);
lean_ctor_set(v___x_337_, 16, v___x_331_);
lean_ctor_set(v___x_337_, 17, v___x_330_);
lean_ctor_set(v___x_337_, 18, v___x_332_);
lean_ctor_set(v___x_337_, 19, v___x_331_);
lean_ctor_set(v___x_337_, 20, v___x_330_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*21, v___x_333_);
return v___x_337_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
return v___x_338_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object* v___y_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = l_String_quote(v___y_340_);
v___x_342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_dec(v_x_343_);
return v_x_344_;
}
else
{
lean_object* v_head_346_; lean_object* v_tail_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_358_; 
v_head_346_ = lean_ctor_get(v_x_345_, 0);
v_tail_347_ = lean_ctor_get(v_x_345_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_349_ = v_x_345_;
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_tail_347_);
lean_inc(v_head_346_);
lean_dec(v_x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
lean_inc(v_x_343_);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 5);
lean_ctor_set(v___x_349_, 1, v_x_343_);
lean_ctor_set(v___x_349_, 0, v_x_344_);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_x_344_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_x_343_);
v___x_352_ = v_reuseFailAlloc_357_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = l_String_quote(v_head_346_);
v___x_354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_352_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v_x_344_ = v___x_355_;
v_x_345_ = v_tail_347_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_dec(v_x_359_);
return v_x_360_;
}
else
{
lean_object* v_head_362_; lean_object* v_tail_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_374_; 
v_head_362_ = lean_ctor_get(v_x_361_, 0);
v_tail_363_ = lean_ctor_get(v_x_361_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_365_ = v_x_361_;
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_tail_363_);
lean_inc(v_head_362_);
lean_dec(v_x_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
lean_inc(v_x_359_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 5);
lean_ctor_set(v___x_365_, 1, v_x_359_);
lean_ctor_set(v___x_365_, 0, v_x_360_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_x_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_x_359_);
v___x_368_ = v_reuseFailAlloc_373_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = l_String_quote(v_head_362_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_368_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_359_, v___x_371_, v_tail_363_);
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v___x_377_; 
lean_dec(v_x_376_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_tail_378_; 
v_tail_378_ = lean_ctor_get(v_x_375_, 1);
if (lean_obj_tag(v_tail_378_) == 0)
{
lean_object* v_head_379_; lean_object* v___x_380_; 
lean_dec(v_x_376_);
v_head_379_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_head_379_);
lean_dec_ref(v_x_375_);
v___x_380_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_379_);
return v___x_380_;
}
else
{
lean_object* v_head_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc(v_tail_378_);
v_head_381_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_head_381_);
lean_dec_ref(v_x_375_);
v___x_382_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_381_);
v___x_383_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_376_, v___x_382_, v_tail_378_);
return v___x_383_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0));
v___x_390_ = lean_string_length(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_array_get_size(v_xs_400_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_nat_dec_eq(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_404_ = lean_array_to_list(v_xs_400_);
v___x_405_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1));
v___x_406_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_404_, v___x_405_);
v___x_407_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4);
v___x_408_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5));
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_406_);
v___x_410_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6));
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_407_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Std_Format_fill(v___x_412_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; 
lean_dec_ref(v_xs_400_);
v___x_414_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8));
return v___x_414_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(11u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(14u);
v___x_436_ = lean_nat_to_int(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(16u);
v___x_444_ = lean_nat_to_int(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(9u);
v___x_452_ = lean_nat_to_int(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(13u);
v___x_459_ = lean_nat_to_int(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(6u);
v___x_466_ = lean_nat_to_int(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(12u);
v___x_473_ = lean_nat_to_int(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(19u);
v___x_481_ = lean_nat_to_int(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_unsigned_to_nat(21u);
v___x_492_ = lean_nat_to_int(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_496_){
_start:
{
lean_object* v_sysroot_497_; lean_object* v_githash_498_; lean_object* v_srcDir_499_; lean_object* v_leanLibDir_500_; lean_object* v_includeDir_501_; lean_object* v_systemLibDir_502_; lean_object* v_binDir_503_; lean_object* v_lean_504_; lean_object* v_leanir_505_; lean_object* v_leanc_506_; lean_object* v_leantar_507_; lean_object* v_sharedLib_508_; lean_object* v_initSharedLib_509_; lean_object* v_ar_510_; lean_object* v_cc_511_; uint8_t v_customCc_512_; lean_object* v_cFlags_513_; lean_object* v_linkStaticFlags_514_; lean_object* v_linkSharedFlags_515_; lean_object* v_ccFlags_516_; lean_object* v_ccLinkStaticFlags_517_; lean_object* v_ccLinkSharedFlags_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_sysroot_497_ = lean_ctor_get(v_x_496_, 0);
lean_inc_ref(v_sysroot_497_);
v_githash_498_ = lean_ctor_get(v_x_496_, 1);
lean_inc_ref(v_githash_498_);
v_srcDir_499_ = lean_ctor_get(v_x_496_, 2);
lean_inc_ref(v_srcDir_499_);
v_leanLibDir_500_ = lean_ctor_get(v_x_496_, 3);
lean_inc_ref(v_leanLibDir_500_);
v_includeDir_501_ = lean_ctor_get(v_x_496_, 4);
lean_inc_ref(v_includeDir_501_);
v_systemLibDir_502_ = lean_ctor_get(v_x_496_, 5);
lean_inc_ref(v_systemLibDir_502_);
v_binDir_503_ = lean_ctor_get(v_x_496_, 6);
lean_inc_ref(v_binDir_503_);
v_lean_504_ = lean_ctor_get(v_x_496_, 7);
lean_inc_ref(v_lean_504_);
v_leanir_505_ = lean_ctor_get(v_x_496_, 8);
lean_inc_ref(v_leanir_505_);
v_leanc_506_ = lean_ctor_get(v_x_496_, 9);
lean_inc_ref(v_leanc_506_);
v_leantar_507_ = lean_ctor_get(v_x_496_, 10);
lean_inc_ref(v_leantar_507_);
v_sharedLib_508_ = lean_ctor_get(v_x_496_, 11);
lean_inc_ref(v_sharedLib_508_);
v_initSharedLib_509_ = lean_ctor_get(v_x_496_, 12);
lean_inc_ref(v_initSharedLib_509_);
v_ar_510_ = lean_ctor_get(v_x_496_, 13);
lean_inc_ref(v_ar_510_);
v_cc_511_ = lean_ctor_get(v_x_496_, 14);
lean_inc_ref(v_cc_511_);
v_customCc_512_ = lean_ctor_get_uint8(v_x_496_, sizeof(void*)*21);
v_cFlags_513_ = lean_ctor_get(v_x_496_, 15);
lean_inc_ref(v_cFlags_513_);
v_linkStaticFlags_514_ = lean_ctor_get(v_x_496_, 16);
lean_inc_ref(v_linkStaticFlags_514_);
v_linkSharedFlags_515_ = lean_ctor_get(v_x_496_, 17);
lean_inc_ref(v_linkSharedFlags_515_);
v_ccFlags_516_ = lean_ctor_get(v_x_496_, 18);
lean_inc_ref(v_ccFlags_516_);
v_ccLinkStaticFlags_517_ = lean_ctor_get(v_x_496_, 19);
lean_inc_ref(v_ccLinkStaticFlags_517_);
v_ccLinkSharedFlags_518_ = lean_ctor_get(v_x_496_, 20);
lean_inc_ref(v_ccLinkSharedFlags_518_);
lean_dec_ref(v_x_496_);
v___x_519_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_520_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_521_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_524_ = l_String_quote(v_sysroot_497_);
v___x_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Repr_addAppParen(v___x_526_, v___x_522_);
v___x_528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_521_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = 0;
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_520_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_519_);
v___x_539_ = l_String_quote(v_githash_498_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_521_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_529_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_538_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_532_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_534_);
v___x_546_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_519_);
v___x_549_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_550_ = l_String_quote(v_srcDir_499_);
v___x_551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_523_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Repr_addAppParen(v___x_552_, v___x_522_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_549_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_529_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_548_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_532_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_534_);
v___x_559_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_519_);
v___x_562_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_563_ = l_String_quote(v_leanLibDir_500_);
v___x_564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_523_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_Repr_addAppParen(v___x_565_, v___x_522_);
v___x_567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_562_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*1, v___x_529_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_561_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_532_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_534_);
v___x_572_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_519_);
v___x_575_ = l_String_quote(v_includeDir_501_);
v___x_576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_523_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Repr_addAppParen(v___x_577_, v___x_522_);
v___x_579_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_562_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_529_);
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_574_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_532_);
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_534_);
v___x_584_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_519_);
v___x_587_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_588_ = l_String_quote(v_systemLibDir_502_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_523_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Repr_addAppParen(v___x_590_, v___x_522_);
v___x_592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_587_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*1, v___x_529_);
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_586_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_532_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_534_);
v___x_597_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_519_);
v___x_600_ = l_String_quote(v_binDir_503_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_523_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Repr_addAppParen(v___x_602_, v___x_522_);
v___x_604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_549_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_529_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_599_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_532_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_534_);
v___x_609_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_519_);
v___x_612_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_613_ = l_String_quote(v_lean_504_);
v___x_614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_523_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Repr_addAppParen(v___x_615_, v___x_522_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_612_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*1, v___x_529_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_611_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_532_);
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_534_);
v___x_622_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_519_);
v___x_625_ = l_String_quote(v_leanir_505_);
v___x_626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_523_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Repr_addAppParen(v___x_627_, v___x_522_);
v___x_629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_549_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_529_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_624_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_532_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_534_);
v___x_634_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_519_);
v___x_637_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_638_ = l_String_quote(v_leanc_506_);
v___x_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_523_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Repr_addAppParen(v___x_640_, v___x_522_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_529_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_636_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_532_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_534_);
v___x_647_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_519_);
v___x_650_ = l_String_quote(v_leantar_507_);
v___x_651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_523_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Repr_addAppParen(v___x_652_, v___x_522_);
v___x_654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_521_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_529_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_649_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_532_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_534_);
v___x_659_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_519_);
v___x_662_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__24, &l_Lake_instReprLeanInstall_repr___redArg___closed__24_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24);
v___x_663_ = l_String_quote(v_sharedLib_508_);
v___x_664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_523_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Repr_addAppParen(v___x_665_, v___x_522_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*1, v___x_529_);
v___x_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_661_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_532_);
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_534_);
v___x_672_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_519_);
v___x_675_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_676_ = l_String_quote(v_initSharedLib_509_);
v___x_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
v___x_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_523_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Repr_addAppParen(v___x_678_, v___x_522_);
v___x_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_675_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_529_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_674_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_532_);
v___x_684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_534_);
v___x_685_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__27));
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_519_);
v___x_688_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__28, &l_Lake_instReprLeanInstall_repr___redArg___closed__28_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28);
v___x_689_ = l_String_quote(v_ar_510_);
v___x_690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_523_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Repr_addAppParen(v___x_691_, v___x_522_);
v___x_693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_688_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_529_);
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_687_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_532_);
v___x_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_534_);
v___x_698_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__29));
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_519_);
v___x_701_ = l_String_quote(v_cc_511_);
v___x_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_523_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Repr_addAppParen(v___x_703_, v___x_522_);
v___x_705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_688_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*1, v___x_529_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_700_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_532_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_534_);
v___x_710_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__31));
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_519_);
v___x_713_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__32, &l_Lake_instReprLeanInstall_repr___redArg___closed__32_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32);
v___x_714_ = l_Bool_repr___redArg(v_customCc_512_);
v___x_715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_529_);
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_712_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_532_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_534_);
v___x_720_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__34));
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_519_);
v___x_723_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_513_);
v___x_724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_549_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*1, v___x_529_);
v___x_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_722_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_532_);
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_534_);
v___x_729_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__36));
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_519_);
v___x_732_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__37, &l_Lake_instReprLeanInstall_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37);
v___x_733_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_514_);
v___x_734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_735_, sizeof(void*)*1, v___x_529_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_731_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_532_);
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_534_);
v___x_739_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__39));
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_519_);
v___x_742_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_515_);
v___x_743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_732_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v___x_529_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_741_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_532_);
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_534_);
v___x_748_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__41));
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_519_);
v___x_751_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_516_);
v___x_752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_521_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v___x_529_);
v___x_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_750_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_532_);
v___x_756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_534_);
v___x_757_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__43));
v___x_758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_519_);
v___x_760_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__44, &l_Lake_instReprLeanInstall_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44);
v___x_761_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_517_);
v___x_762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*1, v___x_529_);
v___x_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_759_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_532_);
v___x_766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_534_);
v___x_767_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__46));
v___x_768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_519_);
v___x_770_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_518_);
v___x_771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_760_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_529_);
v___x_773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_769_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_775_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_773_);
v___x_777_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_774_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*1, v___x_529_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_781_, lean_object* v_prec_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_784_, lean_object* v_prec_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_instReprLeanInstall_repr(v_x_784_, v_prec_785_);
lean_dec(v_prec_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = l_System_Platform_isWindows;
if (v___x_790_ == 0)
{
lean_object* v_leanLibDir_791_; lean_object* v_systemLibDir_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_leanLibDir_791_ = lean_ctor_get(v_self_789_, 3);
v_systemLibDir_792_ = lean_ctor_get(v_self_789_, 5);
v___x_793_ = lean_box(0);
lean_inc_ref(v_systemLibDir_792_);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v_systemLibDir_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
lean_inc_ref(v_leanLibDir_791_);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v_leanLibDir_791_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
return v___x_795_;
}
else
{
lean_object* v_binDir_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_binDir_796_ = lean_ctor_get(v_self_789_, 6);
v___x_797_ = lean_box(0);
lean_inc_ref(v_binDir_796_);
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v_binDir_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lake_LeanInstall_sharedLibPath(v_self_799_);
lean_dec_ref(v_self_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_801_){
_start:
{
uint8_t v_customCc_802_; 
v_customCc_802_ = lean_ctor_get_uint8(v_self_801_, sizeof(void*)*21);
if (v_customCc_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v_cc_804_; lean_object* v___x_805_; 
v_cc_804_ = lean_ctor_get(v_self_801_, 14);
lean_inc_ref(v_cc_804_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_cc_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lake_LeanInstall_leanCc_x3f(v_self_806_);
lean_dec_ref(v_self_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_808_, lean_object* v_self_809_){
_start:
{
if (v_shared_808_ == 0)
{
lean_object* v_ccLinkStaticFlags_810_; 
v_ccLinkStaticFlags_810_ = lean_ctor_get(v_self_809_, 19);
lean_inc_ref(v_ccLinkStaticFlags_810_);
return v_ccLinkStaticFlags_810_;
}
else
{
lean_object* v_ccLinkSharedFlags_811_; 
v_ccLinkSharedFlags_811_ = lean_ctor_get(v_self_809_, 20);
lean_inc_ref(v_ccLinkSharedFlags_811_);
return v_ccLinkSharedFlags_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_812_, lean_object* v_self_813_){
_start:
{
uint8_t v_shared_boxed_814_; lean_object* v_res_815_; 
v_shared_boxed_814_ = lean_unbox(v_shared_812_);
v_res_815_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_814_, v_self_813_);
lean_dec_ref(v_self_813_);
return v_res_815_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = l_System_FilePath_exeExtension;
v___x_818_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_819_ = l_System_FilePath_addExtension(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_820_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = l_Lake_instInhabitedDynlib_default;
v___x_822_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_823_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
lean_ctor_set(v___x_823_, 3, v___x_822_);
lean_ctor_set(v___x_823_, 4, v___x_821_);
lean_ctor_set(v___x_823_, 5, v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
return v___x_824_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_834_){
_start:
{
lean_object* v_home_835_; lean_object* v_srcDir_836_; lean_object* v_binDir_837_; lean_object* v_libDir_838_; lean_object* v_sharedDynlib_839_; lean_object* v_lake_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_home_835_ = lean_ctor_get(v_x_834_, 0);
lean_inc_ref(v_home_835_);
v_srcDir_836_ = lean_ctor_get(v_x_834_, 1);
lean_inc_ref(v_srcDir_836_);
v_binDir_837_ = lean_ctor_get(v_x_834_, 2);
lean_inc_ref(v_binDir_837_);
v_libDir_838_ = lean_ctor_get(v_x_834_, 3);
lean_inc_ref(v_libDir_838_);
v_sharedDynlib_839_ = lean_ctor_get(v_x_834_, 4);
lean_inc_ref(v_sharedDynlib_839_);
v_lake_840_ = lean_ctor_get(v_x_834_, 5);
lean_inc_ref(v_lake_840_);
lean_dec_ref(v_x_834_);
v___x_841_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_842_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_843_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_846_ = l_String_quote(v_home_835_);
v___x_847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_845_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Repr_addAppParen(v___x_848_, v___x_844_);
v___x_850_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_843_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = 0;
v___x_852_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*1, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_842_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_box(1);
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_841_);
v___x_861_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_862_ = l_String_quote(v_srcDir_836_);
v___x_863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_845_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Repr_addAppParen(v___x_864_, v___x_844_);
v___x_866_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_861_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*1, v___x_851_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_860_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_854_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_856_);
v___x_871_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_841_);
v___x_874_ = l_String_quote(v_binDir_837_);
v___x_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_845_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Repr_addAppParen(v___x_876_, v___x_844_);
v___x_878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_861_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_851_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_873_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___x_854_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_856_);
v___x_883_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_841_);
v___x_886_ = l_String_quote(v_libDir_838_);
v___x_887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_845_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Repr_addAppParen(v___x_888_, v___x_844_);
v___x_890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_861_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*1, v___x_851_);
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_885_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_854_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_856_);
v___x_895_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__3));
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_841_);
v___x_898_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_899_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_839_);
v___x_900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_851_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_897_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_854_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_856_);
v___x_905_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__4));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_841_);
v___x_908_ = l_String_quote(v_lake_840_);
v___x_909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_845_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Repr_addAppParen(v___x_910_, v___x_844_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_843_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_851_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_907_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_916_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_914_);
v___x_918_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_915_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_851_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_922_, lean_object* v_prec_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_925_, lean_object* v_prec_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lake_instReprLakeInstall_repr(v_x_925_, v_prec_926_);
lean_dec(v_prec_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_930_){
_start:
{
lean_object* v_sharedDynlib_931_; lean_object* v_path_932_; 
v_sharedDynlib_931_ = lean_ctor_get(v_self_930_, 4);
v_path_932_ = lean_ctor_get(v_sharedDynlib_931_, 0);
lean_inc_ref(v_path_932_);
return v_path_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lake_LakeInstall_sharedLib(v_self_933_);
lean_dec_ref(v_self_933_);
return v_res_934_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__3(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_lib_941_; 
v___x_939_ = l_Lake_sharedLibExt;
v___x_940_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__2));
v_lib_941_ = lean_string_append(v___x_940_, v___x_939_);
return v_lib_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_942_){
_start:
{
lean_object* v_sysroot_943_; lean_object* v_srcDir_944_; lean_object* v_leanLibDir_945_; lean_object* v_binDir_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___y_950_; lean_object* v_lib_958_; uint8_t v___x_959_; 
v_sysroot_943_ = lean_ctor_get(v_lean_942_, 0);
lean_inc_ref(v_sysroot_943_);
v_srcDir_944_ = lean_ctor_get(v_lean_942_, 2);
lean_inc_ref(v_srcDir_944_);
v_leanLibDir_945_ = lean_ctor_get(v_lean_942_, 3);
lean_inc_ref(v_leanLibDir_945_);
v_binDir_946_ = lean_ctor_get(v_lean_942_, 6);
lean_inc_ref(v_binDir_946_);
lean_dec_ref(v_lean_942_);
v___x_947_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_948_ = l_System_FilePath_join(v_srcDir_944_, v___x_947_);
v_lib_958_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__3, &l_Lake_LakeInstall_ofLean___closed__3_once, _init_l_Lake_LakeInstall_ofLean___closed__3);
v___x_959_ = l_System_Platform_isWindows;
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_inc_ref(v_leanLibDir_945_);
v___x_960_ = l_System_FilePath_join(v_leanLibDir_945_, v_lib_958_);
v___y_950_ = v___x_960_;
goto v___jp_949_;
}
else
{
lean_object* v___x_961_; 
lean_inc_ref(v_binDir_946_);
v___x_961_ = l_System_FilePath_join(v_binDir_946_, v_lib_958_);
v___y_950_ = v___x_961_;
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_951_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_952_ = 0;
v___x_953_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_954_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_954_, 0, v___y_950_);
lean_ctor_set(v___x_954_, 1, v___x_951_);
lean_ctor_set(v___x_954_, 2, v___x_953_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*3, v___x_952_);
v___x_955_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_946_);
v___x_956_ = l_System_FilePath_join(v_binDir_946_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_957_, 0, v_sysroot_943_);
lean_ctor_set(v___x_957_, 1, v___x_948_);
lean_ctor_set(v___x_957_, 2, v_binDir_946_);
lean_ctor_set(v___x_957_, 3, v_leanLibDir_945_);
lean_ctor_set(v___x_957_, 4, v___x_954_);
lean_ctor_set(v___x_957_, 5, v___x_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_967_ = lean_io_getenv(v___x_966_);
if (lean_obj_tag(v___x_967_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_995_; 
v_val_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_995_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_995_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_995_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; 
v___x_972_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_973_ = lean_io_getenv(v___x_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_975_ = v___x_993_;
goto v___jp_974_;
}
else
{
lean_object* v_val_994_; 
v_val_994_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v___x_973_);
v___y_975_ = v_val_994_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_startInclusive_980_; lean_object* v_endExclusive_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_string_utf8_byte_size(v___y_975_);
lean_inc_ref(v___y_975_);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v___y_975_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = l_String_Slice_trimAscii(v___x_978_);
v_startInclusive_980_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_startInclusive_980_);
v_endExclusive_981_ = lean_ctor_get(v___x_979_, 2);
lean_inc(v_endExclusive_981_);
lean_dec_ref(v___x_979_);
v___x_982_ = lean_nat_sub(v_endExclusive_981_, v_startInclusive_980_);
lean_dec(v_startInclusive_980_);
lean_dec(v_endExclusive_981_);
v___x_983_ = lean_nat_dec_eq(v___x_982_, v___x_976_);
lean_dec(v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_984_ = ((lean_object*)(l_Lake_leanExe___closed__0));
lean_inc_n(v_val_968_, 2);
v___x_985_ = l_System_FilePath_join(v_val_968_, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__2));
v___x_987_ = l_System_FilePath_join(v_val_968_, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_988_, 0, v_val_968_);
lean_ctor_set(v___x_988_, 1, v___y_975_);
lean_ctor_set(v___x_988_, 2, v___x_985_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_988_);
v___x_990_ = v___x_970_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
lean_object* v___x_992_; 
lean_dec_ref(v___y_975_);
lean_del_object(v___x_970_);
lean_dec(v_val_968_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec(v___x_967_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lake_findElanInstall_x3f();
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1010_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1011_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1015_ = 1;
v___x_1016_ = 0;
v___x_1017_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1017_, 0, v___x_1010_);
lean_ctor_set(v___x_1017_, 1, v_lean_1008_);
lean_ctor_set(v___x_1017_, 2, v___x_1011_);
lean_ctor_set(v___x_1017_, 3, v___x_1012_);
lean_ctor_set(v___x_1017_, 4, v___x_1014_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*5, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*5 + 1, v___x_1016_);
v___x_1018_ = l_IO_Process_output(v___x_1017_, v___x_1012_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1037_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1037_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1037_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint32_t v_exitCode_1023_; lean_object* v_stdout_1024_; uint32_t v___x_1025_; uint8_t v___x_1026_; 
v_exitCode_1023_ = lean_ctor_get_uint32(v_a_1019_, sizeof(void*)*2);
v_stdout_1024_ = lean_ctor_get(v_a_1019_, 0);
lean_inc_ref(v_stdout_1024_);
lean_dec(v_a_1019_);
v___x_1025_ = 0;
v___x_1026_ = lean_uint32_dec_eq(v_exitCode_1023_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec_ref(v_stdout_1024_);
lean_del_object(v___x_1021_);
return v___x_1012_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_str_1030_; lean_object* v_startInclusive_1031_; lean_object* v_endExclusive_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1027_ = lean_string_utf8_byte_size(v_stdout_1024_);
v___x_1028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1028_, 0, v_stdout_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1013_);
lean_ctor_set(v___x_1028_, 2, v___x_1027_);
v___x_1029_ = l_String_Slice_trimAscii(v___x_1028_);
v_str_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_str_1030_);
v_startInclusive_1031_ = lean_ctor_get(v___x_1029_, 1);
lean_inc(v_startInclusive_1031_);
v_endExclusive_1032_ = lean_ctor_get(v___x_1029_, 2);
lean_inc(v_endExclusive_1032_);
lean_dec_ref(v___x_1029_);
v___x_1033_ = lean_string_utf8_extract(v_str_1030_, v_startInclusive_1031_, v_endExclusive_1032_);
lean_dec(v_endExclusive_1032_);
lean_dec(v_startInclusive_1031_);
lean_dec_ref(v_str_1030_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1033_);
v___x_1035_ = v___x_1021_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
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
else
{
lean_dec_ref(v___x_1018_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lake_findLeanSysroot_x3f(v_lean_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1048_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1049_ = l_Lake_leanExe(v_sysroot_1046_);
v___x_1050_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1054_ = 1;
v___x_1055_ = 0;
v___x_1056_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1056_, 0, v___x_1048_);
lean_ctor_set(v___x_1056_, 1, v___x_1049_);
lean_ctor_set(v___x_1056_, 2, v___x_1050_);
lean_ctor_set(v___x_1056_, 3, v___x_1051_);
lean_ctor_set(v___x_1056_, 4, v___x_1053_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*5, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*5 + 1, v___x_1055_);
v___x_1057_ = l_IO_Process_output(v___x_1056_, v___x_1051_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_stdout_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_str_1063_; lean_object* v_startInclusive_1064_; lean_object* v_endExclusive_1065_; lean_object* v___x_1066_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v_stdout_1059_ = lean_ctor_get(v_a_1058_, 0);
lean_inc_ref(v_stdout_1059_);
lean_dec(v_a_1058_);
v___x_1060_ = lean_string_utf8_byte_size(v_stdout_1059_);
v___x_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1061_, 0, v_stdout_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1052_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
v___x_1062_ = l_String_Slice_trimAscii(v___x_1061_);
v_str_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_ref(v_str_1063_);
v_startInclusive_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_startInclusive_1064_);
v_endExclusive_1065_ = lean_ctor_get(v___x_1062_, 2);
lean_inc(v_endExclusive_1065_);
lean_dec_ref(v___x_1062_);
v___x_1066_ = lean_string_utf8_extract(v_str_1063_, v_startInclusive_1064_, v_endExclusive_1065_);
lean_dec(v_endExclusive_1065_);
lean_dec(v_startInclusive_1064_);
lean_dec_ref(v_str_1063_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
lean_dec_ref(v___x_1057_);
v___x_1067_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1076_ = lean_io_getenv(v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 1)
{
lean_object* v_val_1077_; 
lean_dec_ref(v_sysroot_1073_);
v_val_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v___x_1076_);
return v_val_1077_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
lean_dec(v___x_1076_);
v___x_1078_ = l_Lake_leanArExe(v_sysroot_1073_);
v___x_1079_ = l_System_FilePath_pathExists(v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1081_ = lean_io_getenv(v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 1)
{
lean_object* v_val_1082_; 
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1082_);
lean_dec_ref(v___x_1081_);
return v_val_1082_;
}
else
{
lean_object* v___x_1083_; 
lean_dec(v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
return v___x_1083_;
}
}
else
{
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1087_, lean_object* v_i_1088_, lean_object* v_cc_1089_){
_start:
{
lean_object* v_sysroot_1090_; lean_object* v_githash_1091_; lean_object* v_srcDir_1092_; lean_object* v_leanLibDir_1093_; lean_object* v_includeDir_1094_; lean_object* v_systemLibDir_1095_; lean_object* v_binDir_1096_; lean_object* v_lean_1097_; lean_object* v_leanir_1098_; lean_object* v_leanc_1099_; lean_object* v_leantar_1100_; lean_object* v_sharedLib_1101_; lean_object* v_initSharedLib_1102_; lean_object* v_ar_1103_; lean_object* v_cFlags_1104_; lean_object* v_linkStaticFlags_1105_; lean_object* v_linkSharedFlags_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1119_; 
v_sysroot_1090_ = lean_ctor_get(v_i_1088_, 0);
v_githash_1091_ = lean_ctor_get(v_i_1088_, 1);
v_srcDir_1092_ = lean_ctor_get(v_i_1088_, 2);
v_leanLibDir_1093_ = lean_ctor_get(v_i_1088_, 3);
v_includeDir_1094_ = lean_ctor_get(v_i_1088_, 4);
v_systemLibDir_1095_ = lean_ctor_get(v_i_1088_, 5);
v_binDir_1096_ = lean_ctor_get(v_i_1088_, 6);
v_lean_1097_ = lean_ctor_get(v_i_1088_, 7);
v_leanir_1098_ = lean_ctor_get(v_i_1088_, 8);
v_leanc_1099_ = lean_ctor_get(v_i_1088_, 9);
v_leantar_1100_ = lean_ctor_get(v_i_1088_, 10);
v_sharedLib_1101_ = lean_ctor_get(v_i_1088_, 11);
v_initSharedLib_1102_ = lean_ctor_get(v_i_1088_, 12);
v_ar_1103_ = lean_ctor_get(v_i_1088_, 13);
v_cFlags_1104_ = lean_ctor_get(v_i_1088_, 15);
v_linkStaticFlags_1105_ = lean_ctor_get(v_i_1088_, 16);
v_linkSharedFlags_1106_ = lean_ctor_get(v_i_1088_, 17);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_i_1088_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1120_ = lean_ctor_get(v_i_1088_, 20);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_i_1088_, 19);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_i_1088_, 18);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_i_1088_, 14);
lean_dec(v_unused_1123_);
v___x_1108_ = v_i_1088_;
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_linkSharedFlags_1106_);
lean_inc(v_linkStaticFlags_1105_);
lean_inc(v_cFlags_1104_);
lean_inc(v_ar_1103_);
lean_inc(v_initSharedLib_1102_);
lean_inc(v_sharedLib_1101_);
lean_inc(v_leantar_1100_);
lean_inc(v_leanc_1099_);
lean_inc(v_leanir_1098_);
lean_inc(v_lean_1097_);
lean_inc(v_binDir_1096_);
lean_inc(v_systemLibDir_1095_);
lean_inc(v_includeDir_1094_);
lean_inc(v_leanLibDir_1093_);
lean_inc(v_srcDir_1092_);
lean_inc(v_githash_1091_);
lean_inc(v_sysroot_1090_);
lean_dec(v_i_1088_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_ccLinkFlags_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_ccLinkFlags_1110_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1087_);
v___x_1111_ = 0;
v___x_1112_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1087_);
lean_inc_ref(v_cFlags_1104_);
v___x_1113_ = l_Array_append___redArg(v_cFlags_1104_, v___x_1112_);
lean_dec_ref(v___x_1112_);
lean_inc_ref(v_ccLinkFlags_1110_);
v___x_1114_ = l_Array_append___redArg(v_ccLinkFlags_1110_, v_linkStaticFlags_1105_);
v___x_1115_ = l_Array_append___redArg(v_ccLinkFlags_1110_, v_linkSharedFlags_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 20, v___x_1115_);
lean_ctor_set(v___x_1108_, 19, v___x_1114_);
lean_ctor_set(v___x_1108_, 18, v___x_1113_);
lean_ctor_set(v___x_1108_, 14, v_cc_1089_);
v___x_1117_ = v___x_1108_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_sysroot_1090_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_githash_1091_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_srcDir_1092_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_leanLibDir_1093_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_includeDir_1094_);
lean_ctor_set(v_reuseFailAlloc_1118_, 5, v_systemLibDir_1095_);
lean_ctor_set(v_reuseFailAlloc_1118_, 6, v_binDir_1096_);
lean_ctor_set(v_reuseFailAlloc_1118_, 7, v_lean_1097_);
lean_ctor_set(v_reuseFailAlloc_1118_, 8, v_leanir_1098_);
lean_ctor_set(v_reuseFailAlloc_1118_, 9, v_leanc_1099_);
lean_ctor_set(v_reuseFailAlloc_1118_, 10, v_leantar_1100_);
lean_ctor_set(v_reuseFailAlloc_1118_, 11, v_sharedLib_1101_);
lean_ctor_set(v_reuseFailAlloc_1118_, 12, v_initSharedLib_1102_);
lean_ctor_set(v_reuseFailAlloc_1118_, 13, v_ar_1103_);
lean_ctor_set(v_reuseFailAlloc_1118_, 14, v_cc_1089_);
lean_ctor_set(v_reuseFailAlloc_1118_, 15, v_cFlags_1104_);
lean_ctor_set(v_reuseFailAlloc_1118_, 16, v_linkStaticFlags_1105_);
lean_ctor_set(v_reuseFailAlloc_1118_, 17, v_linkSharedFlags_1106_);
lean_ctor_set(v_reuseFailAlloc_1118_, 18, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1118_, 19, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1118_, 20, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*21, v___x_1111_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1124_, lean_object* v_i_1125_, lean_object* v_cc_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1124_, v_i_1125_, v_cc_1126_);
lean_dec_ref(v_sysroot_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1128_, lean_object* v_cc_1129_){
_start:
{
lean_object* v_sysroot_1130_; lean_object* v_githash_1131_; lean_object* v_srcDir_1132_; lean_object* v_leanLibDir_1133_; lean_object* v_includeDir_1134_; lean_object* v_systemLibDir_1135_; lean_object* v_binDir_1136_; lean_object* v_lean_1137_; lean_object* v_leanir_1138_; lean_object* v_leanc_1139_; lean_object* v_leantar_1140_; lean_object* v_sharedLib_1141_; lean_object* v_initSharedLib_1142_; lean_object* v_ar_1143_; uint8_t v_customCc_1144_; lean_object* v_cFlags_1145_; lean_object* v_linkStaticFlags_1146_; lean_object* v_linkSharedFlags_1147_; lean_object* v_ccFlags_1148_; lean_object* v_ccLinkStaticFlags_1149_; lean_object* v_ccLinkSharedFlags_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_sysroot_1130_ = lean_ctor_get(v_i_1128_, 0);
v_githash_1131_ = lean_ctor_get(v_i_1128_, 1);
v_srcDir_1132_ = lean_ctor_get(v_i_1128_, 2);
v_leanLibDir_1133_ = lean_ctor_get(v_i_1128_, 3);
v_includeDir_1134_ = lean_ctor_get(v_i_1128_, 4);
v_systemLibDir_1135_ = lean_ctor_get(v_i_1128_, 5);
v_binDir_1136_ = lean_ctor_get(v_i_1128_, 6);
v_lean_1137_ = lean_ctor_get(v_i_1128_, 7);
v_leanir_1138_ = lean_ctor_get(v_i_1128_, 8);
v_leanc_1139_ = lean_ctor_get(v_i_1128_, 9);
v_leantar_1140_ = lean_ctor_get(v_i_1128_, 10);
v_sharedLib_1141_ = lean_ctor_get(v_i_1128_, 11);
v_initSharedLib_1142_ = lean_ctor_get(v_i_1128_, 12);
v_ar_1143_ = lean_ctor_get(v_i_1128_, 13);
v_customCc_1144_ = lean_ctor_get_uint8(v_i_1128_, sizeof(void*)*21);
v_cFlags_1145_ = lean_ctor_get(v_i_1128_, 15);
v_linkStaticFlags_1146_ = lean_ctor_get(v_i_1128_, 16);
v_linkSharedFlags_1147_ = lean_ctor_get(v_i_1128_, 17);
v_ccFlags_1148_ = lean_ctor_get(v_i_1128_, 18);
v_ccLinkStaticFlags_1149_ = lean_ctor_get(v_i_1128_, 19);
v_ccLinkSharedFlags_1150_ = lean_ctor_get(v_i_1128_, 20);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_i_1128_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_i_1128_, 14);
lean_dec(v_unused_1158_);
v___x_1152_ = v_i_1128_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1150_);
lean_inc(v_ccLinkStaticFlags_1149_);
lean_inc(v_ccFlags_1148_);
lean_inc(v_linkSharedFlags_1147_);
lean_inc(v_linkStaticFlags_1146_);
lean_inc(v_cFlags_1145_);
lean_inc(v_ar_1143_);
lean_inc(v_initSharedLib_1142_);
lean_inc(v_sharedLib_1141_);
lean_inc(v_leantar_1140_);
lean_inc(v_leanc_1139_);
lean_inc(v_leanir_1138_);
lean_inc(v_lean_1137_);
lean_inc(v_binDir_1136_);
lean_inc(v_systemLibDir_1135_);
lean_inc(v_includeDir_1134_);
lean_inc(v_leanLibDir_1133_);
lean_inc(v_srcDir_1132_);
lean_inc(v_githash_1131_);
lean_inc(v_sysroot_1130_);
lean_dec(v_i_1128_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 14, v_cc_1129_);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_sysroot_1130_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_githash_1131_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_srcDir_1132_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_leanLibDir_1133_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_includeDir_1134_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_systemLibDir_1135_);
lean_ctor_set(v_reuseFailAlloc_1156_, 6, v_binDir_1136_);
lean_ctor_set(v_reuseFailAlloc_1156_, 7, v_lean_1137_);
lean_ctor_set(v_reuseFailAlloc_1156_, 8, v_leanir_1138_);
lean_ctor_set(v_reuseFailAlloc_1156_, 9, v_leanc_1139_);
lean_ctor_set(v_reuseFailAlloc_1156_, 10, v_leantar_1140_);
lean_ctor_set(v_reuseFailAlloc_1156_, 11, v_sharedLib_1141_);
lean_ctor_set(v_reuseFailAlloc_1156_, 12, v_initSharedLib_1142_);
lean_ctor_set(v_reuseFailAlloc_1156_, 13, v_ar_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 14, v_cc_1129_);
lean_ctor_set(v_reuseFailAlloc_1156_, 15, v_cFlags_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 16, v_linkStaticFlags_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 17, v_linkSharedFlags_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 18, v_ccFlags_1148_);
lean_ctor_set(v_reuseFailAlloc_1156_, 19, v_ccLinkStaticFlags_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 20, v_ccLinkSharedFlags_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*21, v_customCc_1144_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1161_, lean_object* v_i_1162_){
_start:
{
lean_object* v_cc_1165_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1196_ = lean_io_getenv(v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 1)
{
lean_object* v_val_1197_; 
lean_dec_ref(v_sysroot_1161_);
v_val_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_val_1197_);
lean_dec_ref(v___x_1196_);
v_cc_1165_ = v_val_1197_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
lean_dec(v___x_1196_);
lean_inc_ref(v_sysroot_1161_);
v___x_1198_ = l_Lake_leanCcExe(v_sysroot_1161_);
v___x_1199_ = l_System_FilePath_pathExists(v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_sysroot_1161_);
v___x_1200_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1201_ = lean_io_getenv(v___x_1200_);
if (lean_obj_tag(v___x_1201_) == 1)
{
lean_object* v_val_1202_; 
v_val_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1202_);
lean_dec_ref(v___x_1201_);
v_cc_1165_ = v_val_1202_;
goto v___jp_1164_;
}
else
{
lean_object* v_sysroot_1203_; lean_object* v_githash_1204_; lean_object* v_srcDir_1205_; lean_object* v_leanLibDir_1206_; lean_object* v_includeDir_1207_; lean_object* v_systemLibDir_1208_; lean_object* v_binDir_1209_; lean_object* v_lean_1210_; lean_object* v_leanir_1211_; lean_object* v_leanc_1212_; lean_object* v_leantar_1213_; lean_object* v_sharedLib_1214_; lean_object* v_initSharedLib_1215_; lean_object* v_ar_1216_; uint8_t v_customCc_1217_; lean_object* v_cFlags_1218_; lean_object* v_linkStaticFlags_1219_; lean_object* v_linkSharedFlags_1220_; lean_object* v_ccFlags_1221_; lean_object* v_ccLinkStaticFlags_1222_; lean_object* v_ccLinkSharedFlags_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v___x_1201_);
v_sysroot_1203_ = lean_ctor_get(v_i_1162_, 0);
v_githash_1204_ = lean_ctor_get(v_i_1162_, 1);
v_srcDir_1205_ = lean_ctor_get(v_i_1162_, 2);
v_leanLibDir_1206_ = lean_ctor_get(v_i_1162_, 3);
v_includeDir_1207_ = lean_ctor_get(v_i_1162_, 4);
v_systemLibDir_1208_ = lean_ctor_get(v_i_1162_, 5);
v_binDir_1209_ = lean_ctor_get(v_i_1162_, 6);
v_lean_1210_ = lean_ctor_get(v_i_1162_, 7);
v_leanir_1211_ = lean_ctor_get(v_i_1162_, 8);
v_leanc_1212_ = lean_ctor_get(v_i_1162_, 9);
v_leantar_1213_ = lean_ctor_get(v_i_1162_, 10);
v_sharedLib_1214_ = lean_ctor_get(v_i_1162_, 11);
v_initSharedLib_1215_ = lean_ctor_get(v_i_1162_, 12);
v_ar_1216_ = lean_ctor_get(v_i_1162_, 13);
v_customCc_1217_ = lean_ctor_get_uint8(v_i_1162_, sizeof(void*)*21);
v_cFlags_1218_ = lean_ctor_get(v_i_1162_, 15);
v_linkStaticFlags_1219_ = lean_ctor_get(v_i_1162_, 16);
v_linkSharedFlags_1220_ = lean_ctor_get(v_i_1162_, 17);
v_ccFlags_1221_ = lean_ctor_get(v_i_1162_, 18);
v_ccLinkStaticFlags_1222_ = lean_ctor_get(v_i_1162_, 19);
v_ccLinkSharedFlags_1223_ = lean_ctor_get(v_i_1162_, 20);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_i_1162_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_i_1162_, 14);
lean_dec(v_unused_1232_);
v___x_1225_ = v_i_1162_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1223_);
lean_inc(v_ccLinkStaticFlags_1222_);
lean_inc(v_ccFlags_1221_);
lean_inc(v_linkSharedFlags_1220_);
lean_inc(v_linkStaticFlags_1219_);
lean_inc(v_cFlags_1218_);
lean_inc(v_ar_1216_);
lean_inc(v_initSharedLib_1215_);
lean_inc(v_sharedLib_1214_);
lean_inc(v_leantar_1213_);
lean_inc(v_leanc_1212_);
lean_inc(v_leanir_1211_);
lean_inc(v_lean_1210_);
lean_inc(v_binDir_1209_);
lean_inc(v_systemLibDir_1208_);
lean_inc(v_includeDir_1207_);
lean_inc(v_leanLibDir_1206_);
lean_inc(v_srcDir_1205_);
lean_inc(v_githash_1204_);
lean_inc(v_sysroot_1203_);
lean_dec(v_i_1162_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__1));
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 14, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_sysroot_1203_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_githash_1204_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_srcDir_1205_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_leanLibDir_1206_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_includeDir_1207_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_systemLibDir_1208_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_binDir_1209_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_lean_1210_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_leanir_1211_);
lean_ctor_set(v_reuseFailAlloc_1230_, 9, v_leanc_1212_);
lean_ctor_set(v_reuseFailAlloc_1230_, 10, v_leantar_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 11, v_sharedLib_1214_);
lean_ctor_set(v_reuseFailAlloc_1230_, 12, v_initSharedLib_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 13, v_ar_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 14, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1230_, 15, v_cFlags_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 16, v_linkStaticFlags_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 17, v_linkSharedFlags_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 18, v_ccFlags_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 19, v_ccLinkStaticFlags_1222_);
lean_ctor_set(v_reuseFailAlloc_1230_, 20, v_ccLinkSharedFlags_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*21, v_customCc_1217_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1161_, v_i_1162_, v___x_1198_);
lean_dec_ref(v_sysroot_1161_);
return v___x_1233_;
}
}
v___jp_1164_:
{
lean_object* v_sysroot_1166_; lean_object* v_githash_1167_; lean_object* v_srcDir_1168_; lean_object* v_leanLibDir_1169_; lean_object* v_includeDir_1170_; lean_object* v_systemLibDir_1171_; lean_object* v_binDir_1172_; lean_object* v_lean_1173_; lean_object* v_leanir_1174_; lean_object* v_leanc_1175_; lean_object* v_leantar_1176_; lean_object* v_sharedLib_1177_; lean_object* v_initSharedLib_1178_; lean_object* v_ar_1179_; uint8_t v_customCc_1180_; lean_object* v_cFlags_1181_; lean_object* v_linkStaticFlags_1182_; lean_object* v_linkSharedFlags_1183_; lean_object* v_ccFlags_1184_; lean_object* v_ccLinkStaticFlags_1185_; lean_object* v_ccLinkSharedFlags_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_sysroot_1166_ = lean_ctor_get(v_i_1162_, 0);
v_githash_1167_ = lean_ctor_get(v_i_1162_, 1);
v_srcDir_1168_ = lean_ctor_get(v_i_1162_, 2);
v_leanLibDir_1169_ = lean_ctor_get(v_i_1162_, 3);
v_includeDir_1170_ = lean_ctor_get(v_i_1162_, 4);
v_systemLibDir_1171_ = lean_ctor_get(v_i_1162_, 5);
v_binDir_1172_ = lean_ctor_get(v_i_1162_, 6);
v_lean_1173_ = lean_ctor_get(v_i_1162_, 7);
v_leanir_1174_ = lean_ctor_get(v_i_1162_, 8);
v_leanc_1175_ = lean_ctor_get(v_i_1162_, 9);
v_leantar_1176_ = lean_ctor_get(v_i_1162_, 10);
v_sharedLib_1177_ = lean_ctor_get(v_i_1162_, 11);
v_initSharedLib_1178_ = lean_ctor_get(v_i_1162_, 12);
v_ar_1179_ = lean_ctor_get(v_i_1162_, 13);
v_customCc_1180_ = lean_ctor_get_uint8(v_i_1162_, sizeof(void*)*21);
v_cFlags_1181_ = lean_ctor_get(v_i_1162_, 15);
v_linkStaticFlags_1182_ = lean_ctor_get(v_i_1162_, 16);
v_linkSharedFlags_1183_ = lean_ctor_get(v_i_1162_, 17);
v_ccFlags_1184_ = lean_ctor_get(v_i_1162_, 18);
v_ccLinkStaticFlags_1185_ = lean_ctor_get(v_i_1162_, 19);
v_ccLinkSharedFlags_1186_ = lean_ctor_get(v_i_1162_, 20);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_i_1162_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_i_1162_, 14);
lean_dec(v_unused_1194_);
v___x_1188_ = v_i_1162_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1186_);
lean_inc(v_ccLinkStaticFlags_1185_);
lean_inc(v_ccFlags_1184_);
lean_inc(v_linkSharedFlags_1183_);
lean_inc(v_linkStaticFlags_1182_);
lean_inc(v_cFlags_1181_);
lean_inc(v_ar_1179_);
lean_inc(v_initSharedLib_1178_);
lean_inc(v_sharedLib_1177_);
lean_inc(v_leantar_1176_);
lean_inc(v_leanc_1175_);
lean_inc(v_leanir_1174_);
lean_inc(v_lean_1173_);
lean_inc(v_binDir_1172_);
lean_inc(v_systemLibDir_1171_);
lean_inc(v_includeDir_1170_);
lean_inc(v_leanLibDir_1169_);
lean_inc(v_srcDir_1168_);
lean_inc(v_githash_1167_);
lean_inc(v_sysroot_1166_);
lean_dec(v_i_1162_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 14, v_cc_1165_);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_sysroot_1166_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_githash_1167_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_srcDir_1168_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_leanLibDir_1169_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_includeDir_1170_);
lean_ctor_set(v_reuseFailAlloc_1192_, 5, v_systemLibDir_1171_);
lean_ctor_set(v_reuseFailAlloc_1192_, 6, v_binDir_1172_);
lean_ctor_set(v_reuseFailAlloc_1192_, 7, v_lean_1173_);
lean_ctor_set(v_reuseFailAlloc_1192_, 8, v_leanir_1174_);
lean_ctor_set(v_reuseFailAlloc_1192_, 9, v_leanc_1175_);
lean_ctor_set(v_reuseFailAlloc_1192_, 10, v_leantar_1176_);
lean_ctor_set(v_reuseFailAlloc_1192_, 11, v_sharedLib_1177_);
lean_ctor_set(v_reuseFailAlloc_1192_, 12, v_initSharedLib_1178_);
lean_ctor_set(v_reuseFailAlloc_1192_, 13, v_ar_1179_);
lean_ctor_set(v_reuseFailAlloc_1192_, 14, v_cc_1165_);
lean_ctor_set(v_reuseFailAlloc_1192_, 15, v_cFlags_1181_);
lean_ctor_set(v_reuseFailAlloc_1192_, 16, v_linkStaticFlags_1182_);
lean_ctor_set(v_reuseFailAlloc_1192_, 17, v_linkSharedFlags_1183_);
lean_ctor_set(v_reuseFailAlloc_1192_, 18, v_ccFlags_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 19, v_ccLinkStaticFlags_1185_);
lean_ctor_set(v_reuseFailAlloc_1192_, 20, v_ccLinkSharedFlags_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1192_, sizeof(void*)*21, v_customCc_1180_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1234_, lean_object* v_i_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1234_, v_i_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1240_, uint8_t v_collocated_1241_){
_start:
{
lean_object* v_githash_1244_; 
if (v_collocated_1241_ == 0)
{
lean_object* v___x_1273_; 
lean_inc_ref(v_sysroot_1240_);
v___x_1273_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1240_);
v_githash_1244_ = v___x_1273_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_githash;
v_githash_1244_ = v___x_1274_;
goto v___jp_1243_;
}
v___jp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_inc_ref_n(v_sysroot_1240_, 11);
v___x_1245_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1240_);
v___x_1246_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
v___x_1247_ = l_System_FilePath_join(v_sysroot_1240_, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1249_ = l_System_FilePath_join(v___x_1247_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1251_ = l_System_FilePath_join(v_sysroot_1240_, v___x_1250_);
lean_inc_ref(v___x_1251_);
v___x_1252_ = l_System_FilePath_join(v___x_1251_, v___x_1248_);
v___x_1253_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
v___x_1254_ = l_System_FilePath_join(v_sysroot_1240_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1256_ = l_System_FilePath_join(v_sysroot_1240_, v___x_1255_);
v___x_1257_ = l_Lake_leanExe(v_sysroot_1240_);
v___x_1258_ = l_Lake_leanirExe(v_sysroot_1240_);
v___x_1259_ = l_Lake_leancExe(v_sysroot_1240_);
v___x_1260_ = l_Lake_leantarExe(v_sysroot_1240_);
v___x_1261_ = l_Lake_leanSharedLibDir(v_sysroot_1240_);
v___x_1262_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1261_);
v___x_1263_ = l_System_FilePath_join(v___x_1261_, v___x_1262_);
v___x_1264_ = l_Lake_initSharedLib;
v___x_1265_ = l_System_FilePath_join(v___x_1261_, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__1));
v___x_1267_ = 1;
v___x_1268_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_1269_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_1270_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__5, &l_Lake_instInhabitedLeanInstall_default___closed__5_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__5);
v___x_1271_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1271_, 0, v_sysroot_1240_);
lean_ctor_set(v___x_1271_, 1, v_githash_1244_);
lean_ctor_set(v___x_1271_, 2, v___x_1249_);
lean_ctor_set(v___x_1271_, 3, v___x_1252_);
lean_ctor_set(v___x_1271_, 4, v___x_1254_);
lean_ctor_set(v___x_1271_, 5, v___x_1251_);
lean_ctor_set(v___x_1271_, 6, v___x_1256_);
lean_ctor_set(v___x_1271_, 7, v___x_1257_);
lean_ctor_set(v___x_1271_, 8, v___x_1258_);
lean_ctor_set(v___x_1271_, 9, v___x_1259_);
lean_ctor_set(v___x_1271_, 10, v___x_1260_);
lean_ctor_set(v___x_1271_, 11, v___x_1263_);
lean_ctor_set(v___x_1271_, 12, v___x_1265_);
lean_ctor_set(v___x_1271_, 13, v___x_1245_);
lean_ctor_set(v___x_1271_, 14, v___x_1266_);
lean_ctor_set(v___x_1271_, 15, v___x_1268_);
lean_ctor_set(v___x_1271_, 16, v___x_1269_);
lean_ctor_set(v___x_1271_, 17, v___x_1270_);
lean_ctor_set(v___x_1271_, 18, v___x_1268_);
lean_ctor_set(v___x_1271_, 19, v___x_1269_);
lean_ctor_set(v___x_1271_, 20, v___x_1270_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*21, v___x_1267_);
v___x_1272_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1240_, v___x_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1275_, lean_object* v_collocated_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v_collocated_boxed_1278_; lean_object* v_res_1279_; 
v_collocated_boxed_1278_ = lean_unbox(v_collocated_1276_);
v_res_1279_ = l_Lake_LeanInstall_get(v_sysroot_1275_, v_collocated_boxed_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lake_findLeanSysroot_x3f(v_lean_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1293_; 
v_val_1284_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1293_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = 0;
v___x_1289_ = l_Lake_LeanInstall_get(v_val_1284_, v___x_1288_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_io_app_path();
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = l_System_FilePath_parent(v_a_1301_);
if (lean_obj_tag(v___x_1302_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_val_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_n(v_val_1303_, 2);
lean_dec_ref(v___x_1302_);
v___x_1304_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1305_ = l_System_FilePath_join(v_val_1303_, v___x_1304_);
v___x_1306_ = l_System_FilePath_exeExtension;
v___x_1307_ = l_System_FilePath_addExtension(v___x_1305_, v___x_1306_);
v___x_1308_ = l_System_FilePath_pathExists(v___x_1307_);
lean_dec_ref(v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec(v_val_1303_);
goto v___jp_1298_;
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = l_System_FilePath_parent(v_val_1303_);
return v___x_1309_;
}
}
else
{
lean_dec(v___x_1302_);
goto v___jp_1298_;
}
}
else
{
lean_dec_ref(v___x_1300_);
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_System_FilePath_parent(v_lake_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
return v___x_1313_;
}
else
{
lean_object* v_val_1314_; lean_object* v___x_1315_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = l_System_FilePath_parent(v_val_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1317_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = l_System_FilePath_parent(v_val_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
return v___x_1317_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1319_; 
v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1318_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = l_System_FilePath_parent(v_val_1318_);
return v___x_1319_;
}
}
}
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__1(void){
_start:
{
uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = 0;
v___x_1322_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1323_ = l_Lake_nameToSharedLib(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1325_){
_start:
{
lean_object* v___x_1327_; 
lean_inc_ref(v_lake_1325_);
v___x_1327_ = l_Lake_lakeBuildHome_x3f(v_lake_1325_);
if (lean_obj_tag(v___x_1327_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1352_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_lake_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1332_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1328_, 2);
v___x_1333_ = l_System_FilePath_join(v_val_1328_, v___x_1332_);
v___x_1334_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1333_);
v___x_1335_ = l_System_FilePath_join(v___x_1333_, v___x_1334_);
v___x_1336_ = l_Lake_defaultLeanLibDir;
v___x_1337_ = l_System_FilePath_join(v___x_1333_, v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1339_ = 0;
v___x_1340_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref_n(v___x_1337_, 2);
v___x_1341_ = l_System_FilePath_join(v___x_1337_, v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1343_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1338_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3, v___x_1339_);
v_lake_1344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1344_, 0, v_val_1328_);
lean_ctor_set(v_lake_1344_, 1, v_val_1328_);
lean_ctor_set(v_lake_1344_, 2, v___x_1335_);
lean_ctor_set(v_lake_1344_, 3, v___x_1337_);
lean_ctor_set(v_lake_1344_, 4, v___x_1343_);
lean_ctor_set(v_lake_1344_, 5, v_lake_1325_);
v___x_1345_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__2));
v___x_1346_ = l_System_FilePath_join(v___x_1337_, v___x_1345_);
v___x_1347_ = l_System_FilePath_pathExists(v___x_1346_);
lean_dec_ref(v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref(v_lake_1344_);
lean_del_object(v___x_1330_);
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
else
{
lean_object* v___x_1350_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_lake_1344_);
v___x_1350_ = v___x_1330_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_lake_1344_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1353_; 
lean_dec(v___x_1327_);
lean_dec_ref(v_lake_1325_);
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lake_getLakeInstall_x3f(v_lake_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1361_ = lean_io_getenv(v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1371_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_val_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1366_ = 0;
v___x_1367_ = l_Lake_LeanInstall_get(v_val_1362_, v___x_1366_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1367_);
v___x_1369_ = v___x_1364_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_lean_1375_; 
lean_dec(v___x_1361_);
v___x_1372_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1373_ = lean_io_getenv(v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 1)
{
lean_object* v_val_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_startInclusive_1393_; lean_object* v_endExclusive_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_val_1388_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_n(v_val_1388_, 2);
lean_dec_ref(v___x_1373_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_string_utf8_byte_size(v_val_1388_);
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v_val_1388_);
lean_ctor_set(v___x_1391_, 1, v___x_1389_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
v___x_1392_ = l_String_Slice_trimAscii(v___x_1391_);
v_startInclusive_1393_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_startInclusive_1393_);
v_endExclusive_1394_ = lean_ctor_get(v___x_1392_, 2);
lean_inc(v_endExclusive_1394_);
lean_dec_ref(v___x_1392_);
v___x_1395_ = lean_nat_sub(v_endExclusive_1394_, v_startInclusive_1393_);
lean_dec(v_startInclusive_1393_);
lean_dec(v_endExclusive_1394_);
v___x_1396_ = lean_nat_dec_eq(v___x_1395_, v___x_1389_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
v_lean_1375_ = v_val_1388_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1397_; 
lean_dec(v_val_1388_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
}
else
{
lean_object* v___x_1398_; 
lean_dec(v___x_1373_);
v___x_1398_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v_lean_1375_ = v___x_1398_;
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lake_findLeanSysroot_x3f(v_lean_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1386_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = 0;
v___x_1382_ = l_Lake_LeanInstall_get(v_val_1377_, v___x_1381_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1387_; 
lean_dec(v___x_1376_);
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lake_findLeanInstall_x3f();
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_io_app_path();
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = l_Lake_getLakeInstall_x3f(v_a_1431_);
if (lean_obj_tag(v___x_1432_) == 1)
{
return v___x_1432_;
}
else
{
lean_dec(v___x_1432_);
goto v___jp_1403_;
}
}
else
{
lean_dec_ref(v___x_1430_);
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1405_ = lean_io_getenv(v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1428_; 
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1428_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1428_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1410_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1406_, 2);
v___x_1411_ = l_System_FilePath_join(v_val_1406_, v___x_1410_);
v___x_1412_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1411_);
v___x_1413_ = l_System_FilePath_join(v___x_1411_, v___x_1412_);
v___x_1414_ = l_Lake_defaultLeanLibDir;
v___x_1415_ = l_System_FilePath_join(v___x_1411_, v___x_1414_);
v___x_1416_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1417_ = 0;
v___x_1418_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref(v___x_1415_);
v___x_1419_ = l_System_FilePath_join(v___x_1415_, v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1421_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1416_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*3, v___x_1417_);
v___x_1422_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1413_);
v___x_1423_ = l_System_FilePath_join(v___x_1413_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1424_, 0, v_val_1406_);
lean_ctor_set(v___x_1424_, 1, v_val_1406_);
lean_ctor_set(v___x_1424_, 2, v___x_1413_);
lean_ctor_set(v___x_1424_, 3, v___x_1415_);
lean_ctor_set(v___x_1424_, 4, v___x_1421_);
lean_ctor_set(v___x_1424_, 5, v___x_1423_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1424_);
v___x_1426_ = v___x_1408_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v___x_1429_; 
lean_dec(v___x_1405_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lake_findLakeInstall_x3f();
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = l_Lake_findElanInstall_x3f();
v___x_1438_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1499_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1499_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_val_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1499_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1444_ = lean_io_getenv(v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
goto v___jp_1445_;
}
else
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
v_val_1455_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1444_);
v___x_1456_ = l_Lake_envToBool_x3f(v_val_1455_);
if (lean_obj_tag(v___x_1456_) == 0)
{
goto v___jp_1445_;
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1498_; 
v_val_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1498_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_val_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1498_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_unbox(v_val_1457_);
if (v___x_1461_ == 0)
{
lean_del_object(v___x_1459_);
lean_dec(v_val_1457_);
goto v___jp_1445_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_del_object(v___x_1441_);
v___x_1462_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1463_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
lean_inc_n(v_val_1439_, 9);
v___x_1464_ = l_System_FilePath_join(v_val_1439_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1466_ = l_System_FilePath_join(v___x_1464_, v___x_1465_);
v___x_1467_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1468_ = l_System_FilePath_join(v_val_1439_, v___x_1467_);
lean_inc_ref(v___x_1468_);
v___x_1469_ = l_System_FilePath_join(v___x_1468_, v___x_1465_);
v___x_1470_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
v___x_1471_ = l_System_FilePath_join(v_val_1439_, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1473_ = l_System_FilePath_join(v_val_1439_, v___x_1472_);
v___x_1474_ = l_Lake_leanExe(v_val_1439_);
v___x_1475_ = l_Lake_leanirExe(v_val_1439_);
v___x_1476_ = l_Lake_leancExe(v_val_1439_);
v___x_1477_ = l_Lake_leantarExe(v_val_1439_);
v___x_1478_ = l_Lake_leanSharedLibDir(v_val_1439_);
v___x_1479_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1478_);
v___x_1480_ = l_System_FilePath_join(v___x_1478_, v___x_1479_);
v___x_1481_ = l_Lake_initSharedLib;
v___x_1482_ = l_System_FilePath_join(v___x_1478_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1484_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__1));
v___x_1485_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_1486_ = lean_unbox(v_val_1457_);
v___x_1487_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__5, &l_Lake_instInhabitedLeanInstall_default___closed__5_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__5);
lean_inc_ref(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1489_, 0, v_val_1439_);
lean_ctor_set(v___x_1489_, 1, v___x_1462_);
lean_ctor_set(v___x_1489_, 2, v___x_1466_);
lean_ctor_set(v___x_1489_, 3, v___x_1469_);
lean_ctor_set(v___x_1489_, 4, v___x_1471_);
lean_ctor_set(v___x_1489_, 5, v___x_1468_);
lean_ctor_set(v___x_1489_, 6, v___x_1473_);
lean_ctor_set(v___x_1489_, 7, v___x_1474_);
lean_ctor_set(v___x_1489_, 8, v___x_1475_);
lean_ctor_set(v___x_1489_, 9, v___x_1476_);
lean_ctor_set(v___x_1489_, 10, v___x_1477_);
lean_ctor_set(v___x_1489_, 11, v___x_1480_);
lean_ctor_set(v___x_1489_, 12, v___x_1482_);
lean_ctor_set(v___x_1489_, 13, v___x_1483_);
lean_ctor_set(v___x_1489_, 14, v___x_1484_);
lean_ctor_set(v___x_1489_, 15, v___x_1485_);
lean_ctor_set(v___x_1489_, 16, v___x_1487_);
lean_ctor_set(v___x_1489_, 17, v___x_1488_);
lean_ctor_set(v___x_1489_, 18, v___x_1485_);
lean_ctor_set(v___x_1489_, 19, v___x_1487_);
lean_ctor_set(v___x_1489_, 20, v___x_1488_);
v___x_1490_ = lean_unbox(v_val_1457_);
lean_dec(v_val_1457_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*21, v___x_1490_);
v___x_1491_ = l_Lake_findLeanInstall_x3f();
v___x_1492_ = l_Lake_LakeInstall_ofLean(v___x_1489_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1492_);
v___x_1494_ = v___x_1459_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1491_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1437_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
return v___x_1496_;
}
}
}
}
}
v___jp_1445_:
{
uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = 1;
v___x_1447_ = l_Lake_LeanInstall_get(v_val_1439_, v___x_1446_);
lean_inc_ref(v___x_1447_);
v___x_1448_ = l_Lake_LakeInstall_ofLean(v___x_1447_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1447_);
v___x_1450_ = v___x_1441_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1447_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1448_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1437_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v___x_1438_);
v___x_1500_ = l_Lake_findLeanInstall_x3f();
v___x_1501_ = l_Lake_findLakeInstall_x3f();
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1437_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lake_findInstall_x3f();
return v_res_1505_;
}
}
lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
lean_mark_persistent(l_Lake_leanSharedLib);
l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
lean_mark_persistent(l_Lake_initSharedLib);
l_Lake_instInhabitedLeanInstall_default = _init_l_Lake_instInhabitedLeanInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default);
l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
l_Lake_lakeExe = _init_l_Lake_lakeExe();
lean_mark_persistent(l_Lake_lakeExe);
l_Lake_instInhabitedLakeInstall_default = _init_l_Lake_instInhabitedLakeInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default);
l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_InstallPath(builtin);
}
#ifdef __cplusplus
}
#endif

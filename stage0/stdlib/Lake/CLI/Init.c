// Lean compiler output
// Module: Lake.CLI.Init
// Imports: public import Lake.Config.Env public import Lake.Config.Lang import Lake.Util.Git import Lake.Load.Workspace import Init.Data.String.Modify
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
extern uint32_t l_Lean_idEndEscape;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
extern lean_object* l_Lake_toolchainFileName;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_Git_upstreamBranch;
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
lean_object* l_Lake_toUpperCamelCase(lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static const lean_string_object l_Lake_defaultExeRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l_Lake_defaultExeRoot___closed__0 = (const lean_object*)&l_Lake_defaultExeRoot___closed__0_value;
static const lean_ctor_object l_Lake_defaultExeRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_defaultExeRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 217, 115, 245, 30, 114, 54, 221)}};
static const lean_object* l_Lake_defaultExeRoot___closed__1 = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_defaultExeRoot = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "def hello := \"world\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "-- This module serves as the root of the `"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "` library.\n-- Import modules here that should be built as part of the library.\nimport "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".Basic\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "def main : IO Unit :=\n  IO.println s!\"Hello, world!\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "import Lake\nopen Lake DSL\n\npackage "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " where\n  version := v!\"0.1.0\"\n\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = " where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " where\n  root := `Main\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "name = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "\nversion = \"0.1.0\"\ndefaultTargets = ["};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "]\n\n[[lean_lib]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\n\n[[lean_exe]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nroot = \"Main\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = " where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_exe "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "]\n\n[[lean_exe]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = " where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = " where\n  -- add library configuration options here\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 192, .m_capacity = 192, .m_length = 185, .m_data = " where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "\n\n@[default_target]\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " where\n  -- add any library configuration options here\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "\nversion = \"0.1.0\"\nkeywords = [\"math\"]\ndefaultTargets = ["};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 134, .m_data = "]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\n\n[[lean_lib]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 324, .m_capacity = 324, .m_length = 305, .m_data = " where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`\n    ⟨`relaxedAutoImplicit, false⟩,\n    ⟨`maxSynthPendingDepth, .ofNat 3⟩,\n    ⟨`weak.linter.mathlibStandardSet, true⟩,\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 228, .m_capacity = 228, .m_length = 225, .m_data = "]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\nrelaxedAutoImplicit = false\nweak.linter.mathlibStandardSet = true\nmaxSynthPendingDepth = 3\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "# "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 476, .m_capacity = 476, .m_length = 475, .m_data = "\n\n## GitHub configuration\n\nTo set up your new GitHub repository, follow these steps:\n\n* Under your repository name, click **Settings**.\n* In the **Actions** section of the sidebar, click \"General\".\n* Check the box **Allow GitHub Actions to create and approve pull requests**.\n* Click the **Pages** section of the settings sidebar.\n* In the **Source** dropdown menu, select \"GitHub Actions\".\n\nAfter following the steps above, you can remove this section from the README file.\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 201, .m_capacity = 201, .m_length = 200, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v7\n      - uses: leanprover/lean-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 488, .m_capacity = 488, .m_length = 487, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v7\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1951, .m_capacity = 1951, .m_length = 1950, .m_data = "name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 428, .m_capacity = 428, .m_length = 427, .m_data = "name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.std"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__0 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__1 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__1_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.exe"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__2 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__3 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__3_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.lib"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__4 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__5 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__5_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.InitTemplate.mathLax"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__6 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__7 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__7_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.InitTemplate.math"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__8 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__9 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__9_value;
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__10;
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__11;
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprInitTemplate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprInitTemplate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprInitTemplate___closed__0 = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprInitTemplate = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedInitTemplate;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "std"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__1_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__2_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "math-lax"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__3_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "math"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__4 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__4_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__5_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__6 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__6_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__7 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__7_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__8 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__8_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__9 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake.CLI.Init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "_private.Lake.CLI.Init.0.Lake.escapeName!"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "creating lean-action CI workflow"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".github"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "workflows"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_action_ci.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "created lean-action CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "update.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created Mathlib update CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "create-release.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created create-release CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "create-release CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Mathlib update CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "lean-action CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "creating a new math package with a non-release Lean toolchain; Mathlib may not work properly"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 117, .m_capacity = 117, .m_length = 116, .m_data = "could not create a `lean-toolchain` file for the new package; no known toolchain name for the current Elan/Lean/Lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ".gitignore"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value;
static const lean_array_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to initialize git repository"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Basic.lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "package already initialized"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "illegal package name '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "reserved package name"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_init___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "illegal package name: could not derive one from '"};
static const lean_object* l_Lake_init___closed__0 = (const lean_object*)&l_Lake_init___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = l_Lake_defaultLakeDir;
v___x_7_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0));
v___x_8_ = lean_string_append(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_11_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1);
v___x_12_ = lean_string_append(v___x_11_, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object* v_libName_19_, lean_object* v_libRoot_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_21_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0));
v___x_22_ = lean_string_append(v___x_21_, v_libName_19_);
v___x_23_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1));
v___x_24_ = lean_string_append(v___x_22_, v___x_23_);
v___x_25_ = 1;
v___x_26_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_20_, v___x_25_);
v___x_27_ = lean_string_append(v___x_24_, v___x_26_);
lean_dec_ref(v___x_26_);
v___x_28_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
v___x_29_ = lean_string_append(v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object* v_libName_30_, lean_object* v_libRoot_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v_libName_30_, v_libRoot_31_);
lean_dec_ref(v_libName_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object* v_libRoot_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
v___x_36_ = 1;
v___x_37_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_34_, v___x_36_);
v___x_38_ = lean_string_append(v___x_35_, v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
v___x_40_ = lean_string_append(v___x_38_, v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0(void){
_start:
{
uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = 1;
v___x_42_ = ((lean_object*)(l_Lake_defaultExeRoot));
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1));
v___x_46_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0);
v___x_47_ = lean_string_append(v___x_46_, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object* v_libRoot_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_51_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
v___x_52_ = 1;
v___x_53_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_50_, v___x_52_);
v___x_54_ = lean_string_append(v___x_51_, v___x_53_);
lean_dec_ref(v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0));
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object* v_pkgName_63_, lean_object* v_libRoot_64_, lean_object* v_exeName_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_66_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_67_ = l_String_quote(v_pkgName_63_);
v___x_68_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
v___x_69_ = l_Std_Format_defWidth;
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Std_Format_pretty(v___x_68_, v___x_69_, v___x_70_, v___x_70_);
v___x_72_ = lean_string_append(v___x_66_, v___x_71_);
lean_dec_ref(v___x_71_);
v___x_73_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1));
v___x_74_ = lean_string_append(v___x_72_, v___x_73_);
v___x_75_ = lean_string_append(v___x_74_, v_libRoot_64_);
v___x_76_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2));
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
v___x_78_ = l_String_quote(v_exeName_65_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = l_Std_Format_pretty(v___x_79_, v___x_69_, v___x_70_, v___x_70_);
v___x_81_ = lean_string_append(v___x_77_, v___x_80_);
lean_dec_ref(v___x_80_);
v___x_82_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
v___x_83_ = lean_string_append(v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object* v_pkgName_84_, lean_object* v_libRoot_85_, lean_object* v_exeName_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgName_84_, v_libRoot_85_, v_exeName_86_);
lean_dec_ref(v_libRoot_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object* v_pkgName_93_, lean_object* v_libRoot_94_, lean_object* v_exeName_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_96_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_97_ = l_String_quote(v_pkgName_93_);
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = l_Std_Format_defWidth;
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = l_Std_Format_pretty(v___x_98_, v___x_99_, v___x_100_, v___x_100_);
v___x_102_ = lean_string_append(v___x_96_, v___x_101_);
lean_dec_ref(v___x_101_);
v___x_103_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_104_ = lean_string_append(v___x_102_, v___x_103_);
v___x_105_ = l_String_quote(v_exeName_95_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = l_Std_Format_pretty(v___x_106_, v___x_99_, v___x_100_, v___x_100_);
v___x_108_ = lean_string_append(v___x_104_, v___x_107_);
v___x_109_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
v___x_111_ = l_String_quote(v_libRoot_94_);
v___x_112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
v___x_113_ = l_Std_Format_pretty(v___x_112_, v___x_99_, v___x_100_, v___x_100_);
v___x_114_ = lean_string_append(v___x_110_, v___x_113_);
lean_dec_ref(v___x_113_);
v___x_115_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3));
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
v___x_117_ = lean_string_append(v___x_116_, v___x_107_);
lean_dec_ref(v___x_107_);
v___x_118_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object* v_pkgName_121_, lean_object* v_exeName_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_123_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_124_ = l_String_quote(v_pkgName_121_);
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___x_126_ = l_Std_Format_defWidth;
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Std_Format_pretty(v___x_125_, v___x_126_, v___x_127_, v___x_127_);
v___x_129_ = lean_string_append(v___x_123_, v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = l_String_quote(v_exeName_122_);
v___x_133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
v___x_134_ = l_Std_Format_pretty(v___x_133_, v___x_126_, v___x_127_, v___x_127_);
v___x_135_ = lean_string_append(v___x_131_, v___x_134_);
lean_dec_ref(v___x_134_);
v___x_136_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
v___x_137_ = lean_string_append(v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object* v_pkgName_139_, lean_object* v_exeName_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_141_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_142_ = l_String_quote(v_pkgName_139_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = l_Std_Format_defWidth;
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Std_Format_pretty(v___x_143_, v___x_144_, v___x_145_, v___x_145_);
v___x_147_ = lean_string_append(v___x_141_, v___x_146_);
lean_dec_ref(v___x_146_);
v___x_148_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
v___x_150_ = l_String_quote(v_exeName_140_);
v___x_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = l_Std_Format_pretty(v___x_151_, v___x_144_, v___x_145_, v___x_145_);
v___x_153_ = lean_string_append(v___x_149_, v___x_152_);
v___x_154_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0));
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
v___x_156_ = lean_string_append(v___x_155_, v___x_152_);
lean_dec_ref(v___x_152_);
v___x_157_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object* v_pkgName_161_, lean_object* v_libRoot_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_163_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_164_ = l_String_quote(v_pkgName_161_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Std_Format_defWidth;
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Std_Format_pretty(v___x_165_, v___x_166_, v___x_167_, v___x_167_);
v___x_169_ = lean_string_append(v___x_163_, v___x_168_);
lean_dec_ref(v___x_168_);
v___x_170_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0));
v___x_171_ = lean_string_append(v___x_169_, v___x_170_);
v___x_172_ = lean_string_append(v___x_171_, v_libRoot_162_);
v___x_173_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object* v_pkgName_175_, lean_object* v_libRoot_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgName_175_, v_libRoot_176_);
lean_dec_ref(v_libRoot_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object* v_pkgName_178_, lean_object* v_libRoot_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_180_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_181_ = l_String_quote(v_pkgName_178_);
v___x_182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___x_183_ = l_Std_Format_defWidth;
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Std_Format_pretty(v___x_182_, v___x_183_, v___x_184_, v___x_184_);
v___x_186_ = lean_string_append(v___x_180_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
v___x_189_ = l_String_quote(v_libRoot_179_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = l_Std_Format_pretty(v___x_190_, v___x_183_, v___x_184_, v___x_184_);
v___x_192_ = lean_string_append(v___x_188_, v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_append(v___x_194_, v___x_191_);
lean_dec_ref(v___x_191_);
v___x_196_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_197_ = lean_string_append(v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object* v_pkgName_201_, lean_object* v_libRoot_202_, lean_object* v_rev_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_204_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_205_ = l_String_quote(v_pkgName_201_);
v___x_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = l_Std_Format_defWidth;
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Std_Format_pretty(v___x_206_, v___x_207_, v___x_208_, v___x_208_);
v___x_210_ = lean_string_append(v___x_204_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0));
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
v___x_213_ = l_String_quote(v_rev_203_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = l_Std_Format_pretty(v___x_214_, v___x_207_, v___x_208_, v___x_208_);
v___x_216_ = lean_string_append(v___x_212_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
v___x_219_ = lean_string_append(v___x_218_, v_libRoot_202_);
v___x_220_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object* v_pkgName_222_, lean_object* v_libRoot_223_, lean_object* v_rev_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgName_222_, v_libRoot_223_, v_rev_224_);
lean_dec_ref(v_libRoot_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object* v_pkgName_229_, lean_object* v_libRoot_230_, lean_object* v_rev_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_232_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_233_ = l_String_quote(v_pkgName_229_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = l_Std_Format_defWidth;
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = l_Std_Format_pretty(v___x_234_, v___x_235_, v___x_236_, v___x_236_);
v___x_238_ = lean_string_append(v___x_232_, v___x_237_);
lean_dec_ref(v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
v___x_241_ = l_String_quote(v_libRoot_230_);
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = l_Std_Format_pretty(v___x_242_, v___x_235_, v___x_236_, v___x_236_);
v___x_244_ = lean_string_append(v___x_240_, v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = l_String_quote(v_rev_231_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = l_Std_Format_pretty(v___x_248_, v___x_235_, v___x_236_, v___x_236_);
v___x_250_ = lean_string_append(v___x_246_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
v___x_253_ = lean_string_append(v___x_252_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_254_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object* v_pkgName_257_, lean_object* v_libRoot_258_, lean_object* v_rev_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_260_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_261_ = l_String_quote(v_pkgName_257_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = l_Std_Format_defWidth;
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_Std_Format_pretty(v___x_262_, v___x_263_, v___x_264_, v___x_264_);
v___x_266_ = lean_string_append(v___x_260_, v___x_265_);
lean_dec_ref(v___x_265_);
v___x_267_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0));
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
v___x_269_ = l_String_quote(v_rev_259_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Std_Format_pretty(v___x_270_, v___x_263_, v___x_264_, v___x_264_);
v___x_272_ = lean_string_append(v___x_268_, v___x_271_);
lean_dec_ref(v___x_271_);
v___x_273_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
v___x_275_ = lean_string_append(v___x_274_, v_libRoot_258_);
v___x_276_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object* v_pkgName_278_, lean_object* v_libRoot_279_, lean_object* v_rev_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgName_278_, v_libRoot_279_, v_rev_280_);
lean_dec_ref(v_libRoot_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object* v_pkgName_283_, lean_object* v_libRoot_284_, lean_object* v_rev_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_286_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_287_ = l_String_quote(v_pkgName_283_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = l_Std_Format_defWidth;
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Std_Format_pretty(v___x_288_, v___x_289_, v___x_290_, v___x_290_);
v___x_292_ = lean_string_append(v___x_286_, v___x_291_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = l_String_quote(v_libRoot_284_);
v___x_296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = l_Std_Format_pretty(v___x_296_, v___x_289_, v___x_290_, v___x_290_);
v___x_298_ = lean_string_append(v___x_294_, v___x_297_);
v___x_299_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0));
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
v___x_301_ = l_String_quote(v_rev_285_);
v___x_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = l_Std_Format_pretty(v___x_302_, v___x_289_, v___x_290_, v___x_290_);
v___x_304_ = lean_string_append(v___x_300_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = lean_string_append(v___x_306_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_308_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object* v_pkgName_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
v___x_313_ = lean_string_append(v___x_312_, v_pkgName_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object* v_pkgName_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v_pkgName_314_);
lean_dec_ref(v_pkgName_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object* v_pkgName_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
v___x_319_ = lean_string_append(v___x_318_, v_pkgName_317_);
v___x_320_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object* v_pkgName_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v_pkgName_322_);
lean_dec_ref(v_pkgName_322_);
return v_res_323_;
}
}
lean_object* l_Lake_InitTemplate_ctorIdx___impl(uint8_t v_x_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(v_x_332_);
v___x_334_ = lean_obj_tag_nat(v___x_333_);
lean_dec(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_332_ = stack[0].m_num;
lean_object* v_res_335_;
v_res_335_ = l_Lake_InitTemplate_ctorIdx___impl(v_x_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl___boxed(lean_object* v_x_336_){
_start:
{
uint8_t v_x_4__boxed_337_; lean_object* v_res_338_; 
v_x_4__boxed_337_ = lean_unbox(v_x_336_);
v_res_338_ = l_Lake_InitTemplate_ctorIdx___impl(v_x_4__boxed_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* v_k_339_){
_start:
{
lean_inc(v_k_339_);
return v_k_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_340_);
lean_dec(v_k_340_);
return v_res_341_;
}
}
lean_object* l_Lake_InitTemplate_ctorElim(lean_object* v_motive_342_, lean_object* v_ctorIdx_343_, uint8_t v_t_344_, lean_object* v_h_345_, lean_object* v_k_346_){
_start:
{
lean_inc(v_k_346_);
return v_k_346_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_343_ = stack[1].m_obj;
uint8_t v_t_344_ = stack[2].m_num;
lean_object* v_k_346_ = stack[4].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lake_InitTemplate_ctorElim(lean_box(0), v_ctorIdx_343_, v_t_344_, lean_box(0), v_k_346_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* v_motive_348_, lean_object* v_ctorIdx_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_k_352_){
_start:
{
uint8_t v_t_boxed_353_; lean_object* v_res_354_; 
v_t_boxed_353_ = lean_unbox(v_t_350_);
v_res_354_ = l_Lake_InitTemplate_ctorElim(v_motive_348_, v_ctorIdx_349_, v_t_boxed_353_, v_h_351_, v_k_352_);
lean_dec(v_k_352_);
lean_dec(v_ctorIdx_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* v_std_355_){
_start:
{
lean_inc(v_std_355_);
return v_std_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* v_std_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lake_InitTemplate_std_elim___redArg(v_std_356_);
lean_dec(v_std_356_);
return v_res_357_;
}
}
lean_object* l_Lake_InitTemplate_std_elim(lean_object* v_motive_358_, uint8_t v_t_359_, lean_object* v_h_360_, lean_object* v_std_361_){
_start:
{
lean_inc(v_std_361_);
return v_std_361_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_std_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_359_ = stack[1].m_num;
lean_object* v_std_361_ = stack[3].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lake_InitTemplate_std_elim(lean_box(0), v_t_359_, lean_box(0), v_std_361_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_std_366_){
_start:
{
uint8_t v_t_boxed_367_; lean_object* v_res_368_; 
v_t_boxed_367_ = lean_unbox(v_t_364_);
v_res_368_ = l_Lake_InitTemplate_std_elim(v_motive_363_, v_t_boxed_367_, v_h_365_, v_std_366_);
lean_dec(v_std_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* v_exe_369_){
_start:
{
lean_inc(v_exe_369_);
return v_exe_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* v_exe_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_370_);
lean_dec(v_exe_370_);
return v_res_371_;
}
}
lean_object* l_Lake_InitTemplate_exe_elim(lean_object* v_motive_372_, uint8_t v_t_373_, lean_object* v_h_374_, lean_object* v_exe_375_){
_start:
{
lean_inc(v_exe_375_);
return v_exe_375_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_exe_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_373_ = stack[1].m_num;
lean_object* v_exe_375_ = stack[3].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lake_InitTemplate_exe_elim(lean_box(0), v_t_373_, lean_box(0), v_exe_375_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* v_motive_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_exe_380_){
_start:
{
uint8_t v_t_boxed_381_; lean_object* v_res_382_; 
v_t_boxed_381_ = lean_unbox(v_t_378_);
v_res_382_ = l_Lake_InitTemplate_exe_elim(v_motive_377_, v_t_boxed_381_, v_h_379_, v_exe_380_);
lean_dec(v_exe_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* v_lib_383_){
_start:
{
lean_inc(v_lib_383_);
return v_lib_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* v_lib_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_384_);
lean_dec(v_lib_384_);
return v_res_385_;
}
}
lean_object* l_Lake_InitTemplate_lib_elim(lean_object* v_motive_386_, uint8_t v_t_387_, lean_object* v_h_388_, lean_object* v_lib_389_){
_start:
{
lean_inc(v_lib_389_);
return v_lib_389_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_lib_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_387_ = stack[1].m_num;
lean_object* v_lib_389_ = stack[3].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lake_InitTemplate_lib_elim(lean_box(0), v_t_387_, lean_box(0), v_lib_389_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_lib_394_){
_start:
{
uint8_t v_t_boxed_395_; lean_object* v_res_396_; 
v_t_boxed_395_ = lean_unbox(v_t_392_);
v_res_396_ = l_Lake_InitTemplate_lib_elim(v_motive_391_, v_t_boxed_395_, v_h_393_, v_lib_394_);
lean_dec(v_lib_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* v_mathLax_397_){
_start:
{
lean_inc(v_mathLax_397_);
return v_mathLax_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* v_mathLax_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_398_);
lean_dec(v_mathLax_398_);
return v_res_399_;
}
}
lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* v_motive_400_, uint8_t v_t_401_, lean_object* v_h_402_, lean_object* v_mathLax_403_){
_start:
{
lean_inc(v_mathLax_403_);
return v_mathLax_403_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_mathLax_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_401_ = stack[1].m_num;
lean_object* v_mathLax_403_ = stack[3].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lake_InitTemplate_mathLax_elim(lean_box(0), v_t_401_, lean_box(0), v_mathLax_403_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* v_motive_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_mathLax_408_){
_start:
{
uint8_t v_t_boxed_409_; lean_object* v_res_410_; 
v_t_boxed_409_ = lean_unbox(v_t_406_);
v_res_410_ = l_Lake_InitTemplate_mathLax_elim(v_motive_405_, v_t_boxed_409_, v_h_407_, v_mathLax_408_);
lean_dec(v_mathLax_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* v_math_411_){
_start:
{
lean_inc(v_math_411_);
return v_math_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* v_math_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_InitTemplate_math_elim___redArg(v_math_412_);
lean_dec(v_math_412_);
return v_res_413_;
}
}
lean_object* l_Lake_InitTemplate_math_elim(lean_object* v_motive_414_, uint8_t v_t_415_, lean_object* v_h_416_, lean_object* v_math_417_){
_start:
{
lean_inc(v_math_417_);
return v_math_417_;
}
}
LEAN_EXPORT void l_Lake_InitTemplate_math_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_415_ = stack[1].m_num;
lean_object* v_math_417_ = stack[3].m_obj;
lean_object* v_res_418_;
v_res_418_ = l_Lake_InitTemplate_math_elim(lean_box(0), v_t_415_, lean_box(0), v_math_417_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_math_422_){
_start:
{
uint8_t v_t_boxed_423_; lean_object* v_res_424_; 
v_t_boxed_423_ = lean_unbox(v_t_420_);
v_res_424_ = l_Lake_InitTemplate_math_elim(v_motive_419_, v_t_boxed_423_, v_h_421_, v_math_422_);
lean_dec(v_math_422_);
return v_res_424_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(2u);
v___x_441_ = lean_nat_to_int(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_to_int(v___x_442_);
return v___x_443_;
}
}
lean_object* l_Lake_instReprInitTemplate_repr(uint8_t v_x_444_, lean_object* v_prec_445_){
_start:
{
lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v___y_461_; lean_object* v___y_468_; lean_object* v___y_475_; 
switch(v_x_444_)
{
case 0:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1024u);
v___x_482_ = lean_nat_dec_le(v___x_481_, v_prec_445_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_447_ = v___x_483_;
goto v___jp_446_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_447_ = v___x_484_;
goto v___jp_446_;
}
}
case 1:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1024u);
v___x_486_ = lean_nat_dec_le(v___x_485_, v_prec_445_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_454_ = v___x_487_;
goto v___jp_453_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_454_ = v___x_488_;
goto v___jp_453_;
}
}
case 2:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1024u);
v___x_490_ = lean_nat_dec_le(v___x_489_, v_prec_445_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_461_ = v___x_491_;
goto v___jp_460_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_461_ = v___x_492_;
goto v___jp_460_;
}
}
case 3:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1024u);
v___x_494_ = lean_nat_dec_le(v___x_493_, v_prec_445_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_468_ = v___x_495_;
goto v___jp_467_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_468_ = v___x_496_;
goto v___jp_467_;
}
}
default: 
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1024u);
v___x_498_ = lean_nat_dec_le(v___x_497_, v_prec_445_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_475_ = v___x_499_;
goto v___jp_474_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_475_ = v___x_500_;
goto v___jp_474_;
}
}
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
lean_inc(v___y_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_445_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
lean_inc(v___y_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_445_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
lean_inc(v___y_461_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_445_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
lean_inc(v___y_468_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
v___x_473_ = l_Repr_addAppParen(v___x_472_, v_prec_445_);
return v___x_473_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
lean_inc(v___y_475_);
v___x_477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_477_, 0, v___y_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = 0;
v___x_479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*1, v___x_478_);
v___x_480_ = l_Repr_addAppParen(v___x_479_, v_prec_445_);
return v___x_480_;
}
}
}
LEAN_EXPORT void l_Lake_instReprInitTemplate_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_444_ = stack[0].m_num;
lean_object* v_prec_445_ = stack[1].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lake_instReprInitTemplate_repr(v_x_444_, v_prec_445_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* v_x_502_, lean_object* v_prec_503_){
_start:
{
uint8_t v_x_279__boxed_504_; lean_object* v_res_505_; 
v_x_279__boxed_504_ = lean_unbox(v_x_502_);
v_res_505_ = l_Lake_instReprInitTemplate_repr(v_x_279__boxed_504_, v_prec_503_);
lean_dec(v_prec_503_);
return v_res_505_;
}
}
uint8_t l_Lake_InitTemplate_ofNat(lean_object* v_n_508_){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_dec_le(v_n_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(2u);
v___x_512_ = lean_nat_dec_le(v_n_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = lean_nat_dec_le(v_n_508_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = 4;
return v___x_515_;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 3;
return v___x_516_;
}
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 2;
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_le(v_n_508_, v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 1;
return v___x_520_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = 0;
return v___x_521_;
}
}
}
}
LEAN_EXPORT void l_Lake_InitTemplate_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_508_ = stack[0].m_obj;
uint8_t v_res_522_;
v_res_522_ = l_Lake_InitTemplate_ofNat(v_n_508_);
stack->m_num = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* v_n_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lake_InitTemplate_ofNat(v_n_523_);
lean_dec(v_n_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t v_x_526_, uint8_t v_y_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_528_ = lean_box(v_x_526_);
v___x_529_ = lean_obj_tag_nat(v___x_528_);
lean_dec(v___x_528_);
v___x_530_ = lean_box(v_y_527_);
v___x_531_ = lean_obj_tag_nat(v___x_530_);
lean_dec(v___x_530_);
v___x_532_ = lean_nat_dec_eq(v___x_529_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqInitTemplate_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_526_ = stack[0].m_num;
uint8_t v_y_527_ = stack[1].m_num;
uint8_t v_res_533_;
v_res_533_ = l_Lake_instDecidableEqInitTemplate(v_x_526_, v_y_527_);
stack->m_num = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* v_x_534_, lean_object* v_y_535_){
_start:
{
uint8_t v_x_23__boxed_536_; uint8_t v_y_24__boxed_537_; uint8_t v_res_538_; lean_object* v_r_539_; 
v_x_23__boxed_536_ = lean_unbox(v_x_534_);
v_y_24__boxed_537_ = lean_unbox(v_y_535_);
v_res_538_ = l_Lake_instDecidableEqInitTemplate(v_x_23__boxed_536_, v_y_24__boxed_537_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = 0;
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
v___x_563_ = lean_string_dec_eq(v_x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
v___x_565_ = lean_string_dec_eq(v_x_561_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
v___x_567_ = lean_string_dec_eq(v_x_561_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
v___x_569_ = lean_string_dec_eq(v_x_561_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
v___x_571_ = lean_string_dec_eq(v_x_561_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return v___x_573_;
}
}
else
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return v___x_574_;
}
}
else
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return v___x_575_;
}
}
else
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return v___x_576_;
}
}
else
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lake_InitTemplate_ofString_x3f(v_x_578_);
lean_dec_ref(v_x_578_);
return v_res_579_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void){
_start:
{
uint32_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_idBeginEscape;
v___x_582_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_583_ = lean_string_push(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void){
_start:
{
uint32_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = l_Lean_idEndEscape;
v___x_585_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_586_ = lean_string_push(v___x_585_, v___x_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* v_id_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
v___x_589_ = lean_string_append(v___x_588_, v_id_587_);
v___x_590_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* v_id_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_592_);
lean_dec_ref(v_id_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* v_msg_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_596_ = lean_panic_fn_borrowed(v___x_595_, v_msg_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_600_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_601_ = lean_unsigned_to_nat(23u);
v___x_602_ = lean_unsigned_to_nat(350u);
v___x_603_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_604_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_605_ = l_mkPanicMessageWithDecl(v___x_604_, v___x_603_, v___x_602_, v___x_601_, v___x_600_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_607_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_608_ = lean_unsigned_to_nat(23u);
v___x_609_ = lean_unsigned_to_nat(353u);
v___x_610_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_611_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_612_ = l_mkPanicMessageWithDecl(v___x_611_, v___x_610_, v___x_609_, v___x_608_, v___x_607_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* v_x_613_){
_start:
{
switch(lean_obj_tag(v_x_613_))
{
case 0:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
v___x_615_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_614_);
return v___x_615_;
}
case 1:
{
lean_object* v_pre_616_; 
v_pre_616_ = lean_ctor_get(v_x_613_, 0);
if (lean_obj_tag(v_pre_616_) == 0)
{
lean_object* v_str_617_; lean_object* v___x_618_; 
v_str_617_ = lean_ctor_get(v_x_613_, 1);
v___x_618_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_617_);
return v___x_618_;
}
else
{
lean_object* v_str_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_str_619_ = lean_ctor_get(v_x_613_, 1);
v___x_620_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_616_);
v___x_621_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_622_ = lean_string_append(v___x_620_, v___x_621_);
v___x_623_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_619_);
v___x_624_ = lean_string_append(v___x_622_, v___x_623_);
lean_dec_ref(v___x_623_);
return v___x_624_;
}
}
default: 
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
v___x_626_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_625_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_627_);
lean_dec(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* v_s_629_, lean_object* v_p_630_){
_start:
{
uint32_t v___y_632_; lean_object* v___x_637_; uint8_t v_decide_638_; 
v___x_637_ = lean_string_utf8_byte_size(v_s_629_);
v_decide_638_ = lean_nat_dec_eq(v_p_630_, v___x_637_);
if (v_decide_638_ == 0)
{
uint32_t v___x_639_; uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_string_utf8_get_fast(v_s_629_, v_p_630_);
v___x_640_ = 46;
v___x_641_ = lean_uint32_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
v___y_632_ = v___x_639_;
goto v___jp_631_;
}
else
{
uint32_t v___x_642_; 
v___x_642_ = 45;
v___y_632_ = v___x_642_;
goto v___jp_631_;
}
}
else
{
lean_dec(v_p_630_);
return v_s_629_;
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_inc(v_p_630_);
v___x_633_ = lean_string_utf8_set(v_s_629_, v_p_630_, v___y_632_);
v___x_634_ = l_Char_utf8Size(v___y_632_);
v___x_635_ = lean_nat_add(v_p_630_, v___x_634_);
lean_dec(v___x_634_);
lean_dec(v_p_630_);
v_s_629_ = v___x_633_;
v_p_630_ = v___x_635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* v_name_643_){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = 0;
v___x_645_ = l_Lean_Name_toString(v_name_643_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(v___x_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* v_s_648_, lean_object* v_p_649_){
_start:
{
uint32_t v___y_651_; lean_object* v___x_656_; uint8_t v_decide_657_; 
v___x_656_ = lean_string_utf8_byte_size(v_s_648_);
v_decide_657_ = lean_nat_dec_eq(v_p_649_, v___x_656_);
if (v_decide_657_ == 0)
{
uint32_t v___x_658_; uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_string_utf8_get_fast(v_s_648_, v_p_649_);
v___x_659_ = 65;
v___x_660_ = lean_uint32_dec_le(v___x_659_, v___x_658_);
if (v___x_660_ == 0)
{
v___y_651_ = v___x_658_;
goto v___jp_650_;
}
else
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 90;
v___x_662_ = lean_uint32_dec_le(v___x_658_, v___x_661_);
if (v___x_662_ == 0)
{
v___y_651_ = v___x_658_;
goto v___jp_650_;
}
else
{
uint32_t v___x_663_; uint32_t v___x_664_; 
v___x_663_ = 32;
v___x_664_ = lean_uint32_add(v___x_658_, v___x_663_);
v___y_651_ = v___x_664_;
goto v___jp_650_;
}
}
}
else
{
lean_dec(v_p_649_);
return v_s_648_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc(v_p_649_);
v___x_652_ = lean_string_utf8_set(v_s_648_, v_p_649_, v___y_651_);
v___x_653_ = l_Char_utf8Size(v___y_651_);
v___x_654_ = lean_nat_add(v_p_649_, v___x_653_);
lean_dec(v___x_653_);
lean_dec(v_p_649_);
v_s_648_ = v___x_652_;
v_p_649_ = v___x_654_;
goto _start;
}
}
}
lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_667_, uint8_t v_lang_668_, lean_object* v_pkgName_669_, lean_object* v_root_670_, lean_object* v_leanVer_x3f_671_){
_start:
{
lean_object* v_pkgNameStr_672_; lean_object* v___y_674_; 
v_pkgNameStr_672_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_669_);
if (lean_obj_tag(v_leanVer_x3f_671_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_674_ = v___x_705_;
goto v___jp_673_;
}
else
{
lean_object* v_val_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_val_706_ = lean_ctor_get(v_leanVer_x3f_671_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_leanVer_x3f_671_, 1);
v___x_707_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_708_ = l_Lake_StdVer_toString(v_val_706_);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
lean_dec_ref(v___x_708_);
v___y_674_ = v___x_709_;
goto v___jp_673_;
}
v___jp_673_:
{
switch(v_tmp_667_)
{
case 0:
{
lean_dec_ref(v___y_674_);
if (v_lang_668_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_670_);
lean_dec(v_root_670_);
v___x_676_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_672_);
v___x_677_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_672_, v___x_676_);
v___x_678_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_672_, v___x_675_, v___x_677_);
lean_dec_ref(v___x_675_);
return v___x_678_;
}
else
{
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_679_ = 1;
v___x_680_ = l_Lean_Name_toString(v_root_670_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_672_);
v___x_682_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_672_, v___x_681_);
v___x_683_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_672_, v___x_680_, v___x_682_);
return v___x_683_;
}
}
case 1:
{
lean_dec_ref(v___y_674_);
lean_dec(v_root_670_);
if (v_lang_668_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_672_);
v___x_685_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_672_, v___x_684_);
v___x_686_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_672_, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_672_);
v___x_688_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_672_, v___x_687_);
v___x_689_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_672_, v___x_688_);
return v___x_689_;
}
}
case 2:
{
lean_dec_ref(v___y_674_);
if (v_lang_668_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_670_);
lean_dec(v_root_670_);
v___x_691_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_672_, v___x_690_);
lean_dec_ref(v___x_690_);
return v___x_691_;
}
else
{
uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = 1;
v___x_693_ = l_Lean_Name_toString(v_root_670_, v___x_692_);
v___x_694_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_672_, v___x_693_);
return v___x_694_;
}
}
case 3:
{
if (v_lang_668_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_670_);
lean_dec(v_root_670_);
v___x_696_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_672_, v___x_695_, v___y_674_);
lean_dec_ref(v___x_695_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = 1;
v___x_698_ = l_Lean_Name_toString(v_root_670_, v___x_697_);
v___x_699_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_672_, v___x_698_, v___y_674_);
return v___x_699_;
}
}
default: 
{
if (v_lang_668_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_670_);
lean_dec(v_root_670_);
v___x_701_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_672_, v___x_700_, v___y_674_);
lean_dec_ref(v___x_700_);
return v___x_701_;
}
else
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = 1;
v___x_703_ = l_Lean_Name_toString(v_root_670_, v___x_702_);
v___x_704_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_672_, v___x_703_, v___y_674_);
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_0interp(lean_interpreter_value* stack)
{
uint8_t v_tmp_667_ = stack[0].m_num;
uint8_t v_lang_668_ = stack[1].m_num;
lean_object* v_pkgName_669_ = stack[2].m_obj;
lean_object* v_root_670_ = stack[3].m_obj;
lean_object* v_leanVer_x3f_671_ = stack[4].m_obj;
lean_object* v_res_710_;
v_res_710_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_667_, v_lang_668_, v_pkgName_669_, v_root_670_, v_leanVer_x3f_671_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_711_, lean_object* v_lang_712_, lean_object* v_pkgName_713_, lean_object* v_root_714_, lean_object* v_leanVer_x3f_715_){
_start:
{
uint8_t v_tmp_boxed_716_; uint8_t v_lang_boxed_717_; lean_object* v_res_718_; 
v_tmp_boxed_716_ = lean_unbox(v_tmp_711_);
v_lang_boxed_717_ = lean_unbox(v_lang_712_);
v_res_718_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_716_, v_lang_boxed_717_, v_pkgName_713_, v_root_714_, v_leanVer_x3f_715_);
return v_res_718_;
}
}
lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_744_, uint8_t v_tmp_745_, lean_object* v_a_746_){
_start:
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_748_ = 0;
v___x_749_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_750_ = lean_array_push(v_a_746_, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_752_ = l_Lake_joinRelative(v_dir_744_, v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_754_ = l_Lake_joinRelative(v___x_752_, v___x_753_);
lean_inc_ref(v___x_754_);
v___x_755_ = l_IO_FS_createDirAll(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___y_759_; uint8_t v___x_816_; 
lean_dec_ref_known(v___x_755_, 1);
v___x_756_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_754_);
v___x_757_ = l_Lake_joinRelative(v___x_754_, v___x_756_);
v___x_816_ = l_System_FilePath_pathExists(v___x_757_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_817_ = lean_box(v_tmp_745_);
v___x_818_ = lean_obj_tag_nat(v___x_817_);
lean_dec(v___x_817_);
v___x_819_ = lean_unsigned_to_nat(4u);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_822_ = l_IO_FS_writeFile(v___x_757_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref_known(v___x_822_, 1);
v___y_759_ = v___x_750_;
goto v___jp_758_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_754_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_io_error_to_string(v_a_823_);
v___x_825_ = 3;
v___x_826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*1, v___x_825_);
v___x_827_ = lean_array_get_size(v___x_750_);
v___x_828_ = lean_array_push(v___x_750_, v___x_826_);
v___x_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
return v___x_829_;
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_831_ = l_IO_FS_writeFile(v___x_757_, v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
v___y_759_ = v___x_750_;
goto v___jp_758_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_754_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = lean_io_error_to_string(v_a_832_);
v___x_834_ = 3;
v___x_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = lean_array_get_size(v___x_750_);
v___x_837_ = lean_array_push(v___x_750_, v___x_835_);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___x_757_);
lean_dec_ref(v___x_754_);
v___x_839_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
v___x_840_ = lean_array_push(v___x_750_, v___x_839_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
return v___x_842_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_760_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_761_ = lean_string_append(v___x_760_, v___x_757_);
lean_dec_ref(v___x_757_);
v___x_762_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*1, v___x_748_);
v___x_765_ = lean_array_push(v___y_759_, v___x_764_);
v___x_766_ = lean_box(v_tmp_745_);
v___x_767_ = lean_obj_tag_nat(v___x_766_);
lean_dec(v___x_766_);
v___x_768_ = lean_unsigned_to_nat(4u);
v___x_769_ = lean_nat_dec_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v___x_754_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_765_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(v___x_754_);
v___x_773_ = l_Lake_joinRelative(v___x_754_, v___x_772_);
v___x_774_ = l_System_FilePath_pathExists(v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_776_ = l_IO_FS_writeFile(v___x_773_, v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
lean_dec_ref_known(v___x_776_, 1);
v___x_777_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
v___x_778_ = lean_string_append(v___x_777_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_779_ = lean_string_append(v___x_778_, v___x_762_);
v___x_780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*1, v___x_748_);
v___x_781_ = lean_array_push(v___x_765_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_783_ = l_Lake_joinRelative(v___x_754_, v___x_782_);
v___x_784_ = l_System_FilePath_pathExists(v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_786_ = l_IO_FS_writeFile(v___x_783_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_788_ = lean_string_append(v___x_787_, v___x_783_);
lean_dec_ref(v___x_783_);
v___x_789_ = lean_string_append(v___x_788_, v___x_762_);
v___x_790_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*1, v___x_748_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_array_push(v___x_781_, v___x_790_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
return v___x_793_;
}
else
{
lean_object* v_a_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___x_783_);
v_a_794_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_786_, 1);
v___x_795_ = lean_io_error_to_string(v_a_794_);
v___x_796_ = 3;
v___x_797_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*1, v___x_796_);
v___x_798_ = lean_array_get_size(v___x_781_);
v___x_799_ = lean_array_push(v___x_781_, v___x_797_);
v___x_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v___x_783_);
v___x_801_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
v___x_802_ = lean_array_push(v___x_781_, v___x_801_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
return v___x_804_;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v___x_773_);
lean_dec_ref(v___x_754_);
v_a_805_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_776_, 1);
v___x_806_ = lean_io_error_to_string(v_a_805_);
v___x_807_ = 3;
v___x_808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*1, v___x_807_);
v___x_809_ = lean_array_get_size(v___x_765_);
v___x_810_ = lean_array_push(v___x_765_, v___x_808_);
v___x_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
return v___x_811_;
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v___x_773_);
lean_dec_ref(v___x_754_);
v___x_812_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
v___x_813_ = lean_array_push(v___x_765_, v___x_812_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v___x_754_);
v_a_843_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_755_, 1);
v___x_844_ = lean_io_error_to_string(v_a_843_);
v___x_845_ = 3;
v___x_846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_845_);
v___x_847_ = lean_array_get_size(v___x_750_);
v___x_848_ = lean_array_push(v___x_750_, v___x_846_);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_744_ = stack[0].m_obj;
uint8_t v_tmp_745_ = stack[1].m_num;
lean_object* v_a_746_ = stack[2].m_obj;
lean_object* v_res_850_;
v_res_850_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_744_, v_tmp_745_, v_a_746_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_851_, lean_object* v_tmp_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_tmp_boxed_855_; lean_object* v_res_856_; 
v_tmp_boxed_855_ = lean_unbox(v_tmp_852_);
v_res_856_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_851_, v_tmp_boxed_855_, v_a_853_);
return v_res_856_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_857_, size_t v_i_858_, size_t v_stop_859_, lean_object* v_b_860_, lean_object* v___y_861_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_eq(v_i_858_, v_stop_859_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; size_t v___x_866_; size_t v___x_867_; 
v___x_864_ = lean_array_uget_borrowed(v_as_857_, v_i_858_);
lean_inc_ref(v___y_861_);
lean_inc(v___x_864_);
v___x_865_ = lean_apply_2(v___y_861_, v___x_864_, lean_box(0));
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_858_, v___x_866_);
v_i_858_ = v___x_867_;
v_b_860_ = v___x_865_;
goto _start;
}
else
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_b_860_);
return v___x_869_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_857_ = stack[0].m_obj;
size_t v_i_858_ = stack[1].m_num;
size_t v_stop_859_ = stack[2].m_num;
lean_object* v_b_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v_res_870_;
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_857_, v_i_858_, v_stop_859_, v_b_860_, v___y_861_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_871_, lean_object* v_i_872_, lean_object* v_stop_873_, lean_object* v_b_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; lean_object* v_res_879_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_873_);
lean_dec(v_stop_873_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_871_, v_i_boxed_877_, v_stop_boxed_878_, v_b_874_, v___y_875_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v_as_871_);
return v_res_879_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_894_ = lean_array_get_size(v___x_893_);
return v___x_894_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_nat_dec_lt(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_898_; size_t v___x_899_; 
v___x_898_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_899_ = lean_usize_of_nat(v___x_898_);
return v___x_899_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_905_ = l_Lake_Git_upstreamBranch;
v___x_906_ = lean_string_dec_eq(v___x_905_, v___x_904_);
return v___x_906_;
}
}
lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_914_, lean_object* v_name_915_, uint8_t v_tmp_916_, uint8_t v_lang_917_, lean_object* v_env_918_, uint8_t v_offline_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_952_; lean_object* v___y_953_; uint8_t v_a_954_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v_a_1074_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v_a_1131_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; uint8_t v_a_1161_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v_a_1262_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_configFile_1294_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v_a_1342_; lean_object* v___y_1346_; uint8_t v_a_1347_; lean_object* v___y_1372_; uint8_t v_a_1374_; lean_object* v___x_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; 
v___x_922_ = l_Lake_defaultConfigFile;
v___x_1292_ = l_Lake_ConfigLang_fileExtension(v_lang_917_);
v___x_1293_ = l_System_FilePath_addExtension(v___x_922_, v___x_1292_);
lean_dec_ref(v___x_1292_);
lean_inc_ref(v_dir_914_);
v_configFile_1294_ = l_Lake_joinRelative(v_dir_914_, v___x_1293_);
v___x_1406_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1407_ = l_System_FilePath_pathExists(v_configFile_1294_);
v___x_1408_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1408_ == 0)
{
v_a_1374_ = v___x_1407_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1406_, v___x_1410_, v___x_1411_, v___x_1409_, v_a_920_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_dec_ref_known(v___x_1412_, 1);
v_a_1374_ = v___x_1407_;
goto v___jp_1373_;
}
else
{
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1412_;
}
}
v___jp_923_:
{
if (v_offline_919_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_box(0);
v___x_928_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_914_);
v___x_929_ = l_Lake_joinRelative(v_dir_914_, v___x_928_);
lean_inc_ref(v___x_929_);
v___x_930_ = l_Lake_joinRelative(v___x_929_, v___x_922_);
v___x_931_ = l_Lake_defaultManifestFile;
v___x_932_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_933_ = lean_box(1);
v___x_934_ = l_Lean_Options_empty;
v___x_935_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_936_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_936_, 0, v_env_918_);
lean_ctor_set(v___x_936_, 1, v___x_925_);
lean_ctor_set(v___x_936_, 2, v_dir_914_);
lean_ctor_set(v___x_936_, 3, v___x_926_);
lean_ctor_set(v___x_936_, 4, v___x_927_);
lean_ctor_set(v___x_936_, 5, v___x_928_);
lean_ctor_set(v___x_936_, 6, v___x_929_);
lean_ctor_set(v___x_936_, 7, v___x_922_);
lean_ctor_set(v___x_936_, 8, v___x_930_);
lean_ctor_set(v___x_936_, 9, v___x_925_);
lean_ctor_set(v___x_936_, 10, v___x_931_);
lean_ctor_set(v___x_936_, 11, v___x_932_);
lean_ctor_set(v___x_936_, 12, v___x_933_);
lean_ctor_set(v___x_936_, 13, v___x_934_);
lean_ctor_set(v___x_936_, 14, v___x_935_);
lean_ctor_set(v___x_936_, 15, v___x_935_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*16, v_offline_919_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*16 + 1, v_offline_919_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*16 + 2, v_offline_919_);
v___x_937_ = l_Lean_NameSet_empty;
v___x_938_ = l_Lake_updateManifest(v___x_936_, v___x_937_, v___y_924_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
v___jp_941_:
{
if (lean_obj_tag(v___y_943_) == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_942_);
v___x_945_ = lean_apply_2(v___y_942_, v___x_944_, lean_box(0));
v___y_924_ = v___y_942_;
goto v___jp_923_;
}
else
{
lean_dec_ref_known(v___y_943_, 1);
v___y_924_ = v___y_942_;
goto v___jp_923_;
}
}
v___jp_946_:
{
switch(v_tmp_916_)
{
case 3:
{
v___y_942_ = v___y_948_;
v___y_943_ = v___y_947_;
goto v___jp_941_;
}
case 4:
{
v___y_942_ = v___y_948_;
v___y_943_ = v___y_947_;
goto v___jp_941_;
}
default: 
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v___y_947_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
v___jp_951_:
{
if (v_a_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_952_);
v___x_956_ = lean_apply_2(v___y_952_, v___x_955_, lean_box(0));
v___y_947_ = v___y_953_;
v___y_948_ = v___y_952_;
goto v___jp_946_;
}
else
{
v___y_947_ = v___y_953_;
v___y_948_ = v___y_952_;
goto v___jp_946_;
}
}
v___jp_957_:
{
lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; 
v___x_962_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_914_);
v___x_963_ = l_Lake_joinRelative(v_dir_914_, v___x_962_);
v___x_964_ = 4;
v___x_965_ = lean_io_prim_handle_mk(v___x_963_, v___x_964_);
lean_dec_ref(v___x_963_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_968_ = lean_io_prim_handle_put_str(v_a_966_, v___x_967_);
lean_dec(v_a_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_969_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_914_);
v___x_970_ = l_Lake_joinRelative(v_dir_914_, v___x_969_);
v___x_971_ = lean_string_utf8_byte_size(v___y_958_);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_nat_dec_eq(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref(v___y_960_);
v___x_974_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_975_ = lean_string_append(v___y_958_, v___x_974_);
v___x_976_ = l_IO_FS_writeFile(v___x_970_, v___x_975_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v___x_970_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_dec_ref_known(v___x_976_, 1);
v___y_947_ = v___y_959_;
v___y_948_ = v___y_961_;
goto v___jp_946_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_989_; 
lean_dec(v___y_959_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_989_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_989_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_989_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_981_ = lean_io_error_to_string(v_a_977_);
v___x_982_ = 3;
v___x_983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_982_);
lean_inc_ref(v___y_961_);
v___x_984_ = lean_apply_2(v___y_961_, v___x_983_, lean_box(0));
v___x_985_ = lean_box(0);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_985_);
v___x_987_ = v___x_979_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_githash_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
lean_dec_ref(v___y_958_);
v_githash_990_ = lean_ctor_get(v___y_960_, 1);
lean_inc_ref(v_githash_990_);
lean_dec_ref(v___y_960_);
v___x_991_ = lean_string_utf8_byte_size(v_githash_990_);
lean_dec_ref(v_githash_990_);
v___x_992_ = lean_nat_dec_eq(v___x_991_, v___x_972_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; uint8_t v___x_995_; 
v___x_993_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_994_ = l_System_FilePath_pathExists(v___x_970_);
lean_dec_ref(v___x_970_);
v___x_995_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_995_ == 0)
{
v___y_952_ = v___y_961_;
v___y_953_ = v___y_959_;
v_a_954_ = v___x_994_;
goto v___jp_951_;
}
else
{
lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_996_ = lean_box(0);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_993_, v___x_997_, v___x_998_, v___x_996_, v___y_961_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_dec_ref_known(v___x_999_, 1);
v___y_952_ = v___y_961_;
v___y_953_ = v___y_959_;
v_a_954_ = v___x_994_;
goto v___jp_951_;
}
else
{
lean_dec(v___y_959_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
return v___x_999_;
}
}
}
else
{
lean_dec_ref(v___x_970_);
v___y_947_ = v___y_959_;
v___y_948_ = v___y_961_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v_a_1000_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v___x_968_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_968_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1004_ = lean_io_error_to_string(v_a_1000_);
v___x_1005_ = 3;
v___x_1006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1005_);
lean_inc_ref(v___y_961_);
v___x_1007_ = lean_apply_2(v___y_961_, v___x_1006_, lean_box(0));
v___x_1008_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v_a_1013_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1015_ = v___x_965_;
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_965_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1017_ = lean_io_error_to_string(v_a_1013_);
v___x_1018_ = 3;
v___x_1019_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*1, v___x_1018_);
lean_inc_ref(v___y_961_);
v___x_1020_ = lean_apply_2(v___y_961_, v___x_1019_, lean_box(0));
v___x_1021_ = lean_box(0);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1021_);
v___x_1023_ = v___x_1015_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
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
v___jp_1026_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1027_);
v___x_1032_ = lean_apply_2(v___y_1027_, v___x_1031_, lean_box(0));
v___y_958_ = v___y_1028_;
v___y_959_ = v___y_1029_;
v___y_960_ = v___y_1030_;
v___y_961_ = v___y_1027_;
goto v___jp_957_;
}
v___jp_1033_:
{
if (lean_obj_tag(v___y_1038_) == 0)
{
lean_dec_ref_known(v___y_1038_, 1);
v___y_958_ = v___y_1035_;
v___y_959_ = v___y_1036_;
v___y_960_ = v___y_1037_;
v___y_961_ = v___y_1034_;
goto v___jp_957_;
}
else
{
lean_dec_ref_known(v___y_1038_, 1);
v___y_1027_ = v___y_1034_;
v___y_1028_ = v___y_1035_;
v___y_1029_ = v___y_1036_;
v___y_1030_ = v___y_1037_;
goto v___jp_1026_;
}
}
v___jp_1039_:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = l_Lake_Git_upstreamBranch;
v___x_1045_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_914_);
v___x_1048_ = l_Lake_GitRepo_checkoutBranch(v___x_1044_, v_dir_914_, v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 2);
v___x_1050_ = lean_array_get_size(v_a_1049_);
v___x_1051_ = lean_nat_dec_lt(v___x_1046_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec(v_a_1049_);
v___y_958_ = v___y_1041_;
v___y_959_ = v___y_1042_;
v___y_960_ = v___y_1043_;
v___y_961_ = v___y_1040_;
goto v___jp_957_;
}
else
{
lean_object* v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = lean_usize_of_nat(v___x_1050_);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1049_, v___x_1053_, v___x_1054_, v___x_1052_, v___y_1040_);
lean_dec(v_a_1049_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_dec_ref_known(v___x_1055_, 1);
v___y_958_ = v___y_1041_;
v___y_959_ = v___y_1042_;
v___y_960_ = v___y_1043_;
v___y_961_ = v___y_1040_;
goto v___jp_957_;
}
else
{
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___y_1041_;
v___y_1036_ = v___y_1042_;
v___y_1037_ = v___y_1043_;
v___y_1038_ = v___x_1055_;
goto v___jp_1033_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_a_1056_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1048_, 2);
v___x_1057_ = lean_array_get_size(v_a_1056_);
v___x_1058_ = lean_nat_dec_lt(v___x_1046_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec(v_a_1056_);
v___y_1027_ = v___y_1040_;
v___y_1028_ = v___y_1041_;
v___y_1029_ = v___y_1042_;
v___y_1030_ = v___y_1043_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1057_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1056_, v___x_1060_, v___x_1061_, v___x_1059_, v___y_1040_);
lean_dec(v_a_1056_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec_ref_known(v___x_1062_, 1);
v___y_1027_ = v___y_1040_;
v___y_1028_ = v___y_1041_;
v___y_1029_ = v___y_1042_;
v___y_1030_ = v___y_1043_;
goto v___jp_1026_;
}
else
{
v___y_1034_ = v___y_1040_;
v___y_1035_ = v___y_1041_;
v___y_1036_ = v___y_1042_;
v___y_1037_ = v___y_1043_;
v___y_1038_ = v___x_1062_;
goto v___jp_1033_;
}
}
}
}
else
{
v___y_958_ = v___y_1041_;
v___y_959_ = v___y_1042_;
v___y_960_ = v___y_1043_;
v___y_961_ = v___y_1040_;
goto v___jp_957_;
}
}
v___jp_1063_:
{
if (lean_obj_tag(v___y_1068_) == 0)
{
lean_dec_ref_known(v___y_1068_, 1);
v___y_1040_ = v___y_1064_;
v___y_1041_ = v___y_1065_;
v___y_1042_ = v___y_1066_;
v___y_1043_ = v___y_1067_;
goto v___jp_1039_;
}
else
{
lean_dec_ref_known(v___y_1068_, 1);
v___y_1027_ = v___y_1064_;
v___y_1028_ = v___y_1065_;
v___y_1029_ = v___y_1066_;
v___y_1030_ = v___y_1067_;
goto v___jp_1026_;
}
}
v___jp_1069_:
{
if (v_a_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_914_);
v___x_1077_ = l_Lake_GitRepo_quietInit(v_dir_914_, v___x_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 2);
v___x_1079_ = lean_array_get_size(v_a_1078_);
v___x_1080_ = lean_nat_dec_lt(v___x_1075_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec(v_a_1078_);
v___y_1040_ = v___y_1070_;
v___y_1041_ = v___y_1071_;
v___y_1042_ = v___y_1072_;
v___y_1043_ = v___y_1073_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = lean_usize_of_nat(v___x_1079_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1078_, v___x_1082_, v___x_1083_, v___x_1081_, v___y_1070_);
lean_dec(v_a_1078_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref_known(v___x_1084_, 1);
v___y_1040_ = v___y_1070_;
v___y_1041_ = v___y_1071_;
v___y_1042_ = v___y_1072_;
v___y_1043_ = v___y_1073_;
goto v___jp_1039_;
}
else
{
v___y_1064_ = v___y_1070_;
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___x_1084_;
goto v___jp_1063_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_a_1085_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1077_, 2);
v___x_1086_ = lean_array_get_size(v_a_1085_);
v___x_1087_ = lean_nat_dec_lt(v___x_1075_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_a_1085_);
v___y_1027_ = v___y_1070_;
v___y_1028_ = v___y_1071_;
v___y_1029_ = v___y_1072_;
v___y_1030_ = v___y_1073_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = lean_usize_of_nat(v___x_1086_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1085_, v___x_1089_, v___x_1090_, v___x_1088_, v___y_1070_);
lean_dec(v_a_1085_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_dec_ref_known(v___x_1091_, 1);
v___y_1027_ = v___y_1070_;
v___y_1028_ = v___y_1071_;
v___y_1029_ = v___y_1072_;
v___y_1030_ = v___y_1073_;
goto v___jp_1026_;
}
else
{
v___y_1064_ = v___y_1070_;
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___x_1091_;
goto v___jp_1063_;
}
}
}
}
else
{
v___y_958_ = v___y_1071_;
v___y_959_ = v___y_1072_;
v___y_960_ = v___y_1073_;
v___y_961_ = v___y_1070_;
goto v___jp_957_;
}
}
v___jp_1092_:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_914_);
v___x_1098_ = l_Lake_GitRepo_insideWorkTree(v_dir_914_);
v___x_1099_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1099_ == 0)
{
v___y_1070_ = v___y_1096_;
v___y_1071_ = v___y_1093_;
v___y_1072_ = v___y_1094_;
v___y_1073_ = v___y_1095_;
v_a_1074_ = v___x_1098_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1097_, v___x_1101_, v___x_1102_, v___x_1100_, v___y_1096_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
v___y_1070_ = v___y_1096_;
v___y_1071_ = v___y_1093_;
v___y_1072_ = v___y_1094_;
v___y_1073_ = v___y_1095_;
v_a_1074_ = v___x_1098_;
goto v___jp_1069_;
}
else
{
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
return v___x_1103_;
}
}
}
v___jp_1104_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_IO_FS_writeFile(v___y_1109_, v___y_1110_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1109_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_dec_ref_known(v___x_1111_, 1);
v___y_1093_ = v___y_1106_;
v___y_1094_ = v___y_1107_;
v___y_1095_ = v___y_1108_;
v___y_1096_ = v___y_1105_;
goto v___jp_1092_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_env_918_);
lean_dec_ref(v_dir_914_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1116_ = lean_io_error_to_string(v_a_1112_);
v___x_1117_ = 3;
v___x_1118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*1, v___x_1117_);
lean_inc_ref(v___y_1105_);
v___x_1119_ = lean_apply_2(v___y_1105_, v___x_1118_, lean_box(0));
v___x_1120_ = lean_box(0);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1120_);
v___x_1122_ = v___x_1114_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
v___jp_1125_:
{
if (v_a_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_box(v_tmp_916_);
v___x_1133_ = lean_obj_tag_nat(v___x_1132_);
lean_dec(v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(4u);
v___x_1135_ = lean_nat_dec_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_915_);
v___x_1137_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1136_);
lean_dec_ref(v___x_1136_);
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1127_;
v___y_1107_ = v___y_1128_;
v___y_1108_ = v___y_1130_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___x_1137_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_915_);
v___x_1139_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1138_);
lean_dec_ref(v___x_1138_);
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1127_;
v___y_1107_ = v___y_1128_;
v___y_1108_ = v___y_1130_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___x_1139_;
goto v___jp_1104_;
}
}
else
{
lean_dec_ref(v___y_1129_);
lean_dec(v_name_915_);
v___y_1093_ = v___y_1127_;
v___y_1094_ = v___y_1128_;
v___y_1095_ = v___y_1130_;
v___y_1096_ = v___y_1126_;
goto v___jp_1092_;
}
}
v___jp_1140_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1145_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_914_);
v___x_1146_ = l_Lake_joinRelative(v_dir_914_, v___x_1145_);
v___x_1147_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1148_ = l_System_FilePath_pathExists(v___x_1146_);
v___x_1149_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1149_ == 0)
{
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___y_1142_;
v___y_1129_ = v___x_1146_;
v___y_1130_ = v___y_1143_;
v_a_1131_ = v___x_1148_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1147_, v___x_1151_, v___x_1152_, v___x_1150_, v___y_1144_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_dec_ref_known(v___x_1153_, 1);
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___y_1142_;
v___y_1129_ = v___x_1146_;
v___y_1130_ = v___y_1143_;
v_a_1131_ = v___x_1148_;
goto v___jp_1125_;
}
else
{
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1153_;
}
}
}
v___jp_1154_:
{
if (v_a_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1162_ = lean_box(v_tmp_916_);
v___x_1163_ = lean_obj_tag_nat(v___x_1162_);
lean_dec(v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1155_);
v___x_1167_ = l_IO_FS_writeFile(v___y_1158_, v___x_1166_);
lean_dec_ref(v___x_1166_);
lean_dec_ref(v___y_1158_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_dec_ref_known(v___x_1167_, 1);
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1159_;
v___y_1143_ = v___y_1160_;
v___y_1144_ = v___y_1156_;
goto v___jp_1140_;
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1180_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1172_ = lean_io_error_to_string(v_a_1168_);
v___x_1173_ = 3;
v___x_1174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1, v___x_1173_);
lean_inc_ref(v___y_1156_);
v___x_1175_ = lean_apply_2(v___y_1156_, v___x_1174_, lean_box(0));
v___x_1176_ = lean_box(0);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1176_);
v___x_1178_ = v___x_1170_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___y_1155_);
v___x_1181_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1182_ = l_IO_FS_writeFile(v___y_1158_, v___x_1181_);
lean_dec_ref(v___y_1158_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_dec_ref_known(v___x_1182_, 1);
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1159_;
v___y_1143_ = v___y_1160_;
v___y_1144_ = v___y_1156_;
goto v___jp_1140_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1187_ = lean_io_error_to_string(v_a_1183_);
v___x_1188_ = 3;
v___x_1189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1, v___x_1188_);
lean_inc_ref(v___y_1156_);
v___x_1190_ = lean_apply_2(v___y_1156_, v___x_1189_, lean_box(0));
v___x_1191_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1191_);
v___x_1193_ = v___x_1185_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1155_);
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1159_;
v___y_1143_ = v___y_1160_;
v___y_1144_ = v___y_1156_;
goto v___jp_1140_;
}
}
v___jp_1196_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1202_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_914_);
v___x_1203_ = l_Lake_joinRelative(v_dir_914_, v___x_1202_);
v___x_1204_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1205_ = l_System_FilePath_pathExists(v___x_1203_);
v___x_1206_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1206_ == 0)
{
v___y_1155_ = v___y_1197_;
v___y_1156_ = v___y_1198_;
v___y_1157_ = v___y_1199_;
v___y_1158_ = v___x_1203_;
v___y_1159_ = v___y_1200_;
v___y_1160_ = v___y_1201_;
v_a_1161_ = v___x_1205_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1204_, v___x_1208_, v___x_1209_, v___x_1207_, v___y_1198_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec_ref_known(v___x_1210_, 1);
v___y_1155_ = v___y_1197_;
v___y_1156_ = v___y_1198_;
v___y_1157_ = v___y_1199_;
v___y_1158_ = v___x_1203_;
v___y_1159_ = v___y_1200_;
v___y_1160_ = v___y_1201_;
v_a_1161_ = v___x_1205_;
goto v___jp_1154_;
}
else
{
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1197_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1210_;
}
}
}
v___jp_1211_:
{
switch(v_tmp_916_)
{
case 0:
{
v___y_1197_ = v___y_1212_;
v___y_1198_ = v___y_1216_;
v___y_1199_ = v___y_1213_;
v___y_1200_ = v___y_1214_;
v___y_1201_ = v___y_1215_;
goto v___jp_1196_;
}
case 1:
{
v___y_1197_ = v___y_1212_;
v___y_1198_ = v___y_1216_;
v___y_1199_ = v___y_1213_;
v___y_1200_ = v___y_1214_;
v___y_1201_ = v___y_1215_;
goto v___jp_1196_;
}
default: 
{
lean_dec(v___y_1212_);
v___y_1141_ = v___y_1213_;
v___y_1142_ = v___y_1214_;
v___y_1143_ = v___y_1215_;
v___y_1144_ = v___y_1216_;
goto v___jp_1140_;
}
}
}
v___jp_1217_:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_IO_FS_writeFile(v___y_1223_, v___y_1224_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec_ref_known(v___x_1225_, 1);
v___y_1212_ = v___y_1219_;
v___y_1213_ = v___y_1220_;
v___y_1214_ = v___y_1221_;
v___y_1215_ = v___y_1222_;
v___y_1216_ = v___y_1218_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1230_ = lean_io_error_to_string(v_a_1226_);
v___x_1231_ = 3;
v___x_1232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*1, v___x_1231_);
lean_inc_ref(v___y_1218_);
v___x_1233_ = lean_apply_2(v___y_1218_, v___x_1232_, lean_box(0));
v___x_1234_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1234_);
v___x_1236_ = v___x_1228_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
v___jp_1239_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1246_ = lean_box(v_tmp_916_);
v___x_1247_ = lean_obj_tag_nat(v___x_1246_);
lean_dec(v___x_1246_);
v___x_1248_ = lean_unsigned_to_nat(4u);
v___x_1249_ = lean_nat_dec_eq(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = 1;
lean_inc_n(v___y_1240_, 2);
v___x_1251_ = l_Lean_Name_toString(v___y_1240_, v___x_1250_);
v___x_1252_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1251_, v___y_1240_);
lean_dec_ref(v___x_1251_);
v___y_1218_ = v___y_1245_;
v___y_1219_ = v___y_1240_;
v___y_1220_ = v___y_1241_;
v___y_1221_ = v___y_1242_;
v___y_1222_ = v___y_1243_;
v___y_1223_ = v___y_1244_;
v___y_1224_ = v___x_1252_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1253_; 
lean_inc(v___y_1240_);
v___x_1253_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1240_);
v___y_1218_ = v___y_1245_;
v___y_1219_ = v___y_1240_;
v___y_1220_ = v___y_1241_;
v___y_1221_ = v___y_1242_;
v___y_1222_ = v___y_1243_;
v___y_1223_ = v___y_1244_;
v___y_1224_ = v___x_1253_;
goto v___jp_1217_;
}
}
v___jp_1254_:
{
if (v_a_1262_ == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = l_IO_FS_createDirAll(v___y_1255_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1263_, 1);
v___x_1264_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1265_ = l_IO_FS_writeFile(v___y_1260_, v___x_1264_);
lean_dec_ref(v___y_1260_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref_known(v___x_1265_, 1);
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1261_;
v___y_1245_ = v_a_920_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v___y_1261_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1270_ = lean_io_error_to_string(v_a_1266_);
v___x_1271_ = 3;
v___x_1272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*1, v___x_1271_);
lean_inc_ref(v_a_920_);
v___x_1273_ = lean_apply_2(v_a_920_, v___x_1272_, lean_box(0));
v___x_1274_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1279_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1281_ = v___x_1263_;
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1263_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1283_ = lean_io_error_to_string(v_a_1279_);
v___x_1284_ = 3;
v___x_1285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*1, v___x_1284_);
lean_inc_ref(v_a_920_);
v___x_1286_ = lean_apply_2(v_a_920_, v___x_1285_, lean_box(0));
v___x_1287_ = lean_box(0);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1287_);
v___x_1289_ = v___x_1281_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1255_);
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1261_;
v___y_1245_ = v_a_920_;
goto v___jp_1239_;
}
}
v___jp_1295_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_inc(v___y_1300_);
lean_inc(v___y_1296_);
lean_inc(v_name_915_);
v___x_1301_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_916_, v_lang_917_, v_name_915_, v___y_1296_, v___y_1300_);
v___x_1302_ = l_IO_FS_writeFile(v_configFile_1294_, v___x_1301_);
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_configFile_1294_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref_known(v___x_1302_, 1);
if (lean_obj_tag(v___y_1298_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; uint8_t v___x_1310_; 
v_val_1303_ = lean_ctor_get(v___y_1298_, 0);
lean_inc_n(v_val_1303_, 2);
lean_dec_ref_known(v___y_1298_, 1);
v___x_1304_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1305_ = l_System_FilePath_withExtension(v_val_1303_, v___x_1304_);
v___x_1306_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1305_);
v___x_1307_ = l_Lake_joinRelative(v___x_1305_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1309_ = l_System_FilePath_pathExists(v___x_1307_);
v___x_1310_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1310_ == 0)
{
v___y_1255_ = v___x_1305_;
v___y_1256_ = v___y_1296_;
v___y_1257_ = v___y_1297_;
v___y_1258_ = v___y_1300_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___x_1307_;
v___y_1261_ = v_val_1303_;
v_a_1262_ = v___x_1309_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1308_, v___x_1312_, v___x_1313_, v___x_1311_, v_a_920_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_dec_ref_known(v___x_1314_, 1);
v___y_1255_ = v___x_1305_;
v___y_1256_ = v___y_1296_;
v___y_1257_ = v___y_1297_;
v___y_1258_ = v___y_1300_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___x_1307_;
v___y_1261_ = v_val_1303_;
v_a_1262_ = v___x_1309_;
goto v___jp_1254_;
}
else
{
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___x_1305_);
lean_dec(v_val_1303_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1314_;
}
}
}
else
{
lean_dec(v___y_1298_);
v___y_1212_ = v___y_1296_;
v___y_1213_ = v___y_1297_;
v___y_1214_ = v___y_1300_;
v___y_1215_ = v___y_1299_;
v___y_1216_ = v_a_920_;
goto v___jp_1211_;
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_a_1315_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1317_ = v___x_1302_;
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1302_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1319_ = lean_io_error_to_string(v_a_1315_);
v___x_1320_ = 3;
v___x_1321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*1, v___x_1320_);
lean_inc_ref(v_a_920_);
v___x_1322_ = lean_apply_2(v_a_920_, v___x_1321_, lean_box(0));
v___x_1323_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1323_);
v___x_1325_ = v___x_1317_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
v___jp_1328_:
{
lean_object* v_lean_1331_; lean_object* v_toolchain_1332_; lean_object* v___x_1333_; 
v_lean_1331_ = lean_ctor_get(v_env_918_, 1);
v_toolchain_1332_ = lean_ctor_get(v_env_918_, 19);
lean_inc_ref(v_toolchain_1332_);
v___x_1333_ = l_Lake_ToolchainVer_ofString(v_toolchain_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_ver_1334_; lean_object* v___x_1335_; 
v_ver_1334_ = lean_ctor_get(v___x_1333_, 1);
lean_inc_ref(v_ver_1334_);
lean_dec_ref_known(v___x_1333_, 2);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_ver_1334_);
lean_inc_ref(v_lean_1331_);
lean_inc_ref(v_toolchain_1332_);
v___y_1296_ = v_fst_1329_;
v___y_1297_ = v_toolchain_1332_;
v___y_1298_ = v_snd_1330_;
v___y_1299_ = v_lean_1331_;
v___y_1300_ = v___x_1335_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1333_);
v___x_1336_ = lean_box(0);
lean_inc_ref(v_lean_1331_);
lean_inc_ref(v_toolchain_1332_);
v___y_1296_ = v_fst_1329_;
v___y_1297_ = v_toolchain_1332_;
v___y_1298_ = v_snd_1330_;
v___y_1299_ = v_lean_1331_;
v___y_1300_ = v___x_1336_;
goto v___jp_1295_;
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_box(0);
lean_inc(v_name_915_);
v_fst_1329_ = v_name_915_;
v_snd_1330_ = v___x_1338_;
goto v___jp_1328_;
}
v___jp_1339_:
{
if (v_a_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___y_1340_);
v_fst_1329_ = v___y_1341_;
v_snd_1330_ = v___x_1343_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v___y_1340_);
v___x_1344_ = lean_box(0);
v_fst_1329_ = v___y_1341_;
v_snd_1330_ = v___x_1344_;
goto v___jp_1328_;
}
}
v___jp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1348_ = lean_box(v_tmp_916_);
v___x_1349_ = lean_obj_tag_nat(v___x_1348_);
lean_dec(v___x_1348_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
if (v_a_1347_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; uint8_t v___x_1356_; 
lean_inc(v_name_915_);
v___x_1352_ = l_Lake_toUpperCamelCase(v_name_915_);
lean_inc(v___x_1352_);
v___x_1353_ = l_Lean_modToFilePath(v_dir_914_, v___x_1352_, v___y_1346_);
v___x_1354_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1355_ = l_System_FilePath_pathExists(v___x_1353_);
v___x_1356_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1356_ == 0)
{
v___y_1340_ = v___x_1353_;
v___y_1341_ = v___x_1352_;
v_a_1342_ = v___x_1355_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1354_, v___x_1358_, v___x_1359_, v___x_1357_, v_a_920_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
v___y_1340_ = v___x_1353_;
v___y_1341_ = v___x_1352_;
v_a_1342_ = v___x_1355_;
goto v___jp_1339_;
}
else
{
lean_dec_ref(v___x_1353_);
lean_dec(v___x_1352_);
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1360_;
}
}
}
else
{
goto v___jp_1337_;
}
}
else
{
goto v___jp_1337_;
}
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; uint8_t v___x_1366_; 
v___x_1362_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_915_);
v___x_1363_ = l_Lean_modToFilePath(v_dir_914_, v_name_915_, v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1365_ = l_System_FilePath_pathExists(v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1366_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1366_ == 0)
{
v___y_1346_ = v___x_1362_;
v_a_1347_ = v___x_1365_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1367_ = lean_box(0);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1364_, v___x_1368_, v___x_1369_, v___x_1367_, v_a_920_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_dec_ref_known(v___x_1370_, 1);
v___y_1346_ = v___x_1362_;
v_a_1347_ = v___x_1365_;
goto v___jp_1345_;
}
else
{
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___x_1370_;
}
}
}
v___jp_1371_:
{
if (lean_obj_tag(v___y_1372_) == 0)
{
lean_dec_ref_known(v___y_1372_, 1);
goto v___jp_1361_;
}
else
{
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
return v___y_1372_;
}
}
v___jp_1373_:
{
if (v_a_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_914_);
v___x_1377_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_914_, v_tmp_916_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 2);
v___x_1379_ = lean_array_get_size(v_a_1378_);
v___x_1380_ = lean_nat_dec_lt(v___x_1375_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_dec(v_a_1378_);
goto v___jp_1361_;
}
else
{
lean_object* v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1379_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1378_, v___x_1382_, v___x_1383_, v___x_1381_, v_a_920_);
lean_dec(v_a_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
goto v___jp_1361_;
}
else
{
v___y_1372_ = v___x_1384_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1377_, 2);
v___x_1386_ = lean_array_get_size(v_a_1385_);
v___x_1387_ = lean_nat_dec_lt(v___x_1375_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_a_1385_);
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = lean_usize_of_nat(v___x_1386_);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1385_, v___x_1391_, v___x_1392_, v___x_1390_, v_a_920_);
lean_dec(v_a_1385_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1401_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 1);
lean_ctor_set(v___x_1395_, 0, v___x_1390_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1390_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
v___y_1372_ = v___x_1393_;
goto v___jp_1371_;
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_configFile_1294_);
lean_dec_ref(v_env_918_);
lean_dec(v_name_915_);
lean_dec_ref(v_dir_914_);
v___x_1402_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_920_);
v___x_1403_ = lean_apply_2(v_a_920_, v___x_1402_, lean_box(0));
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Init_0__Lake_initPkg_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_914_ = stack[0].m_obj;
lean_object* v_name_915_ = stack[1].m_obj;
uint8_t v_tmp_916_ = stack[2].m_num;
uint8_t v_lang_917_ = stack[3].m_num;
lean_object* v_env_918_ = stack[4].m_obj;
uint8_t v_offline_919_ = stack[5].m_num;
lean_object* v_a_920_ = stack[6].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_914_, v_name_915_, v_tmp_916_, v_lang_917_, v_env_918_, v_offline_919_, v_a_920_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1414_, lean_object* v_name_1415_, lean_object* v_tmp_1416_, lean_object* v_lang_1417_, lean_object* v_env_1418_, lean_object* v_offline_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
uint8_t v_tmp_boxed_1422_; uint8_t v_lang_boxed_1423_; uint8_t v_offline_boxed_1424_; lean_object* v_res_1425_; 
v_tmp_boxed_1422_ = lean_unbox(v_tmp_1416_);
v_lang_boxed_1423_ = lean_unbox(v_lang_1417_);
v_offline_boxed_1424_ = lean_unbox(v_offline_1419_);
v_res_1425_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1414_, v_name_1415_, v_tmp_boxed_1422_, v_lang_boxed_1423_, v_env_1418_, v_offline_boxed_1424_, v_a_1420_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(lean_object* v_a_1426_, lean_object* v_x_1427_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = 0;
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; uint8_t v___x_1431_; 
v_head_1429_ = lean_ctor_get(v_x_1427_, 0);
v_tail_1430_ = lean_ctor_get(v_x_1427_, 1);
v___x_1431_ = lean_string_dec_eq(v_a_1426_, v_head_1429_);
if (v___x_1431_ == 0)
{
v_x_1427_ = v_tail_1430_;
goto _start;
}
else
{
return v___x_1431_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1426_ = stack[0].m_obj;
lean_object* v_x_1427_ = stack[1].m_obj;
uint8_t v_res_1433_;
v_res_1433_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v_a_1426_, v_x_1427_);
stack->m_num = v_res_1433_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3___boxed(lean_object* v_a_1434_, lean_object* v_x_1435_){
_start:
{
uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_res_1436_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v_a_1434_, v_x_1435_);
lean_dec(v_x_1435_);
lean_dec_ref(v_a_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1438_, lean_object* v_pos_1439_){
_start:
{
lean_object* v_str_1440_; lean_object* v_startInclusive_1441_; lean_object* v_endExclusive_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v_decide_1446_; 
v_str_1440_ = lean_ctor_get(v_s_1438_, 0);
v_startInclusive_1441_ = lean_ctor_get(v_s_1438_, 1);
v_endExclusive_1442_ = lean_ctor_get(v_s_1438_, 2);
v___x_1443_ = lean_nat_add(v_startInclusive_1441_, v_pos_1439_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_nat_sub(v_endExclusive_1442_, v___x_1443_);
v_decide_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
lean_dec(v___x_1445_);
if (v_decide_1446_ == 0)
{
uint32_t v___x_1447_; uint32_t v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = lean_string_utf8_get_fast(v_str_1440_, v___x_1443_);
v___x_1448_ = 46;
v___x_1449_ = lean_uint32_dec_eq(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec(v___x_1443_);
return v_pos_1439_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1450_ = lean_string_utf8_next_fast(v_str_1440_, v___x_1443_);
v___x_1451_ = lean_nat_sub(v___x_1450_, v___x_1443_);
lean_dec(v___x_1443_);
v___x_1452_ = lean_nat_add(v_pos_1439_, v___x_1451_);
lean_dec(v___x_1451_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v_pos_1439_, v___x_1453_);
v___x_1455_ = lean_nat_dec_le(v___x_1454_, v___x_1452_);
lean_dec(v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec(v___x_1452_);
return v_pos_1439_;
}
else
{
lean_dec(v_pos_1439_);
v_pos_1439_ = v___x_1452_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1443_);
return v_pos_1439_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1457_, lean_object* v_pos_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1457_, v_pos_1458_);
lean_dec_ref(v_s_1457_);
return v_res_1459_;
}
}
uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(uint32_t v_a_1460_, lean_object* v_x_1461_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
uint8_t v___x_1462_; 
v___x_1462_ = 0;
return v___x_1462_;
}
else
{
lean_object* v_head_1463_; lean_object* v_tail_1464_; uint32_t v___x_1465_; uint8_t v___x_1466_; 
v_head_1463_ = lean_ctor_get(v_x_1461_, 0);
v_tail_1464_ = lean_ctor_get(v_x_1461_, 1);
v___x_1465_ = lean_unbox_uint32(v_head_1463_);
v___x_1466_ = lean_uint32_dec_eq(v_a_1460_, v___x_1465_);
if (v___x_1466_ == 0)
{
v_x_1461_ = v_tail_1464_;
goto _start;
}
else
{
return v___x_1466_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1460_ = stack[0].m_num;
lean_object* v_x_1461_ = stack[1].m_obj;
uint8_t v_res_1468_;
v_res_1468_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_a_1460_, v_x_1461_);
stack->m_num = v_res_1468_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_a_1469_, lean_object* v_x_1470_){
_start:
{
uint32_t v_a_boxed_1471_; uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_a_boxed_1471_ = lean_unbox_uint32(v_a_1469_);
lean_dec(v_a_1469_);
v_res_1472_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_a_boxed_1471_, v_x_1470_);
lean_dec(v_x_1470_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = 92;
v___x_1475_ = lean_box_uint32(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1;
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = 47;
v___x_1480_ = lean_box_uint32(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0);
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1;
v___x_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
return v___x_1483_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(lean_object* v_s_1484_, lean_object* v_a_1485_, uint8_t v_b_1486_){
_start:
{
lean_object* v_str_1487_; lean_object* v_startInclusive_1488_; lean_object* v_endExclusive_1489_; lean_object* v___x_1490_; uint8_t v_decide_1491_; 
v_str_1487_ = lean_ctor_get(v_s_1484_, 0);
v_startInclusive_1488_ = lean_ctor_get(v_s_1484_, 1);
v_endExclusive_1489_ = lean_ctor_get(v_s_1484_, 2);
v___x_1490_ = lean_nat_sub(v_endExclusive_1489_, v_startInclusive_1488_);
v_decide_1491_ = lean_nat_dec_eq(v_a_1485_, v___x_1490_);
lean_dec(v___x_1490_);
if (v_decide_1491_ == 0)
{
lean_object* v___x_1492_; uint32_t v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1492_ = lean_nat_add(v_startInclusive_1488_, v_a_1485_);
lean_dec(v_a_1485_);
v___x_1493_ = lean_string_utf8_get_fast(v_str_1487_, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1);
v___x_1495_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_string_utf8_next_fast(v_str_1487_, v___x_1492_);
lean_dec(v___x_1492_);
v___x_1497_ = lean_nat_sub(v___x_1496_, v_startInclusive_1488_);
v_a_1485_ = v___x_1497_;
v_b_1486_ = v___x_1495_;
goto _start;
}
else
{
lean_dec(v___x_1492_);
return v___x_1495_;
}
}
else
{
lean_dec(v_a_1485_);
return v_b_1486_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1484_ = stack[0].m_obj;
lean_object* v_a_1485_ = stack[1].m_obj;
uint8_t v_b_1486_ = stack[2].m_num;
uint8_t v_res_1499_;
v_res_1499_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1484_, v_a_1485_, v_b_1486_);
stack->m_num = v_res_1499_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___boxed(lean_object* v_s_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
uint8_t v_b_boxed_1503_; uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_b_boxed_1503_ = lean_unbox(v_b_1502_);
v_res_1504_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1500_, v_a_1501_, v_b_boxed_1503_);
lean_dec_ref(v_s_1500_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object* v_s_1506_){
_start:
{
lean_object* v_searcher_1507_; uint8_t v___x_1508_; uint8_t v___x_1509_; 
v_searcher_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = 0;
v___x_1509_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1506_, v_searcher_1507_, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1506_ = stack[0].m_obj;
uint8_t v_res_1510_;
v_res_1510_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v_s_1506_);
stack->m_num = v_res_1510_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object* v_s_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v_s_1511_);
lean_dec_ref(v_s_1511_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = lean_string_utf8_byte_size(v_pkgName_1534_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_nat_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v_decide_1552_; 
lean_inc_ref(v_pkgName_1534_);
v___x_1550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1550_, 0, v_pkgName_1534_);
lean_ctor_set(v___x_1550_, 1, v___x_1548_);
lean_ctor_set(v___x_1550_, 2, v___x_1547_);
v___x_1551_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1550_, v___x_1548_);
v_decide_1552_ = lean_nat_dec_eq(v___x_1551_, v___x_1547_);
lean_dec(v___x_1551_);
if (v_decide_1552_ == 0)
{
uint8_t v___x_1553_; 
v___x_1553_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v___x_1550_);
lean_dec_ref_known(v___x_1550_, 3);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1534_, v___x_1548_);
v___x_1555_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7));
v___x_1556_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v___x_1554_, v___x_1555_);
lean_dec_ref(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v_a_1535_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9));
v___x_1560_ = lean_array_get_size(v_a_1535_);
v___x_1561_ = lean_array_push(v_a_1535_, v___x_1559_);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
return v___x_1562_;
}
}
else
{
goto v___jp_1537_;
}
}
else
{
lean_dec_ref_known(v___x_1550_, 3);
goto v___jp_1537_;
}
}
else
{
goto v___jp_1537_;
}
v___jp_1537_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1538_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1539_ = lean_string_append(v___x_1538_, v_pkgName_1534_);
lean_dec_ref(v_pkgName_1534_);
v___x_1540_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
v___x_1542_ = 3;
v___x_1543_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*1, v___x_1542_);
v___x_1544_ = lean_array_get_size(v_a_1535_);
v___x_1545_ = lean_array_push(v_a_1535_, v___x_1543_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Init_0__Lake_validatePkgName_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgName_1534_ = stack[0].m_obj;
lean_object* v_a_1535_ = stack[1].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1534_, v_a_1535_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1564_, v_a_1565_);
return v_res_1567_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object* v_s_1568_, lean_object* v_inst_1569_, lean_object* v_R_1570_, lean_object* v_a_1571_, uint8_t v_b_1572_, lean_object* v_c_1573_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1568_, v_a_1571_, v_b_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1568_ = stack[0].m_obj;
lean_object* v_a_1571_ = stack[3].m_obj;
uint8_t v_b_1572_ = stack[4].m_num;
uint8_t v_res_1575_;
v_res_1575_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(v_s_1568_, lean_box(0), lean_box(0), v_a_1571_, v_b_1572_, lean_box(0));
stack->m_num = v_res_1575_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object* v_s_1576_, lean_object* v_inst_1577_, lean_object* v_R_1578_, lean_object* v_a_1579_, lean_object* v_b_1580_, lean_object* v_c_1581_){
_start:
{
uint8_t v_b_boxed_1582_; uint8_t v_res_1583_; lean_object* v_r_1584_; 
v_b_boxed_1582_ = lean_unbox(v_b_1580_);
v_res_1583_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(v_s_1576_, v_inst_1577_, v_R_1578_, v_a_1579_, v_b_boxed_1582_, v_c_1581_);
lean_dec_ref(v_s_1576_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1585_, lean_object* v_dir_1586_, lean_object* v_name_1587_, uint8_t v_tmp_1588_, uint8_t v_lang_1589_, lean_object* v_env_1590_, uint8_t v_offline_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v___y_1595_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1623_; lean_object* v___y_1624_; uint8_t v_a_1625_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; uint8_t v_a_1745_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v_a_1802_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v_a_1832_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v_a_1933_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v_configFile_1965_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v_a_2013_; lean_object* v___y_2017_; uint8_t v_a_2018_; lean_object* v___y_2043_; uint8_t v_a_2045_; lean_object* v___x_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; 
v___x_1593_ = l_Lake_defaultConfigFile;
v___x_1963_ = l_Lake_ConfigLang_fileExtension(v_lang_1589_);
v___x_1964_ = l_System_FilePath_addExtension(v___x_1593_, v___x_1963_);
lean_dec_ref(v___x_1963_);
lean_inc_ref(v_dir_1586_);
v_configFile_1965_ = l_Lake_joinRelative(v_dir_1586_, v___x_1964_);
v___x_2077_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2078_ = l_System_FilePath_pathExists(v_configFile_1965_);
v___x_2079_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2079_ == 0)
{
v_a_2045_ = v___x_2078_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2077_, v___x_2081_, v___x_2082_, v___x_2080_, v_a_1585_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_dec_ref_known(v___x_2083_, 1);
v_a_2045_ = v___x_2078_;
goto v___jp_2044_;
}
else
{
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_2083_;
}
}
v___jp_1594_:
{
if (v_offline_1591_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = lean_box(0);
v___x_1599_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1586_);
v___x_1600_ = l_Lake_joinRelative(v_dir_1586_, v___x_1599_);
lean_inc_ref(v___x_1600_);
v___x_1601_ = l_Lake_joinRelative(v___x_1600_, v___x_1593_);
v___x_1602_ = l_Lake_defaultManifestFile;
v___x_1603_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1604_ = lean_box(1);
v___x_1605_ = l_Lean_Options_empty;
v___x_1606_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1607_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_1607_, 0, v_env_1590_);
lean_ctor_set(v___x_1607_, 1, v___x_1596_);
lean_ctor_set(v___x_1607_, 2, v_dir_1586_);
lean_ctor_set(v___x_1607_, 3, v___x_1597_);
lean_ctor_set(v___x_1607_, 4, v___x_1598_);
lean_ctor_set(v___x_1607_, 5, v___x_1599_);
lean_ctor_set(v___x_1607_, 6, v___x_1600_);
lean_ctor_set(v___x_1607_, 7, v___x_1593_);
lean_ctor_set(v___x_1607_, 8, v___x_1601_);
lean_ctor_set(v___x_1607_, 9, v___x_1596_);
lean_ctor_set(v___x_1607_, 10, v___x_1602_);
lean_ctor_set(v___x_1607_, 11, v___x_1603_);
lean_ctor_set(v___x_1607_, 12, v___x_1604_);
lean_ctor_set(v___x_1607_, 13, v___x_1605_);
lean_ctor_set(v___x_1607_, 14, v___x_1606_);
lean_ctor_set(v___x_1607_, 15, v___x_1606_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*16, v_offline_1591_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*16 + 1, v_offline_1591_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*16 + 2, v_offline_1591_);
v___x_1608_ = l_Lean_NameSet_empty;
v___x_1609_ = l_Lake_updateManifest(v___x_1607_, v___x_1608_, v___y_1595_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
v___jp_1612_:
{
if (lean_obj_tag(v___y_1613_) == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1614_);
v___x_1616_ = lean_apply_2(v___y_1614_, v___x_1615_, lean_box(0));
v___y_1595_ = v___y_1614_;
goto v___jp_1594_;
}
else
{
lean_dec_ref_known(v___y_1613_, 1);
v___y_1595_ = v___y_1614_;
goto v___jp_1594_;
}
}
v___jp_1617_:
{
switch(v_tmp_1588_)
{
case 3:
{
v___y_1613_ = v___y_1618_;
v___y_1614_ = v___y_1619_;
goto v___jp_1612_;
}
case 4:
{
v___y_1613_ = v___y_1618_;
v___y_1614_ = v___y_1619_;
goto v___jp_1612_;
}
default: 
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v___y_1618_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
}
v___jp_1622_:
{
if (v_a_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1624_);
v___x_1627_ = lean_apply_2(v___y_1624_, v___x_1626_, lean_box(0));
v___y_1618_ = v___y_1623_;
v___y_1619_ = v___y_1624_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___y_1623_;
v___y_1619_ = v___y_1624_;
goto v___jp_1617_;
}
}
v___jp_1628_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1633_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1586_);
v___x_1634_ = l_Lake_joinRelative(v_dir_1586_, v___x_1633_);
v___x_1635_ = 4;
v___x_1636_ = lean_io_prim_handle_mk(v___x_1634_, v___x_1635_);
lean_dec_ref(v___x_1634_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1639_ = lean_io_prim_handle_put_str(v_a_1637_, v___x_1638_);
lean_dec(v_a_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
lean_dec_ref_known(v___x_1639_, 1);
v___x_1640_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1586_);
v___x_1641_ = l_Lake_joinRelative(v_dir_1586_, v___x_1640_);
v___x_1642_ = lean_string_utf8_byte_size(v___y_1631_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_nat_dec_eq(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v___y_1629_);
v___x_1645_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1646_ = lean_string_append(v___y_1631_, v___x_1645_);
v___x_1647_ = l_IO_FS_writeFile(v___x_1641_, v___x_1646_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v___x_1641_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref_known(v___x_1647_, 1);
v___y_1618_ = v___y_1630_;
v___y_1619_ = v___y_1632_;
goto v___jp_1617_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v___y_1630_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1660_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1660_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1652_ = lean_io_error_to_string(v_a_1648_);
v___x_1653_ = 3;
v___x_1654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set_uint8(v___x_1654_, sizeof(void*)*1, v___x_1653_);
lean_inc_ref(v___y_1632_);
v___x_1655_ = lean_apply_2(v___y_1632_, v___x_1654_, lean_box(0));
v___x_1656_ = lean_box(0);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1656_);
v___x_1658_ = v___x_1650_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_githash_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
lean_dec_ref(v___y_1631_);
v_githash_1661_ = lean_ctor_get(v___y_1629_, 1);
lean_inc_ref(v_githash_1661_);
lean_dec_ref(v___y_1629_);
v___x_1662_ = lean_string_utf8_byte_size(v_githash_1661_);
lean_dec_ref(v_githash_1661_);
v___x_1663_ = lean_nat_dec_eq(v___x_1662_, v___x_1643_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; uint8_t v___x_1665_; uint8_t v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1665_ = l_System_FilePath_pathExists(v___x_1641_);
lean_dec_ref(v___x_1641_);
v___x_1666_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1666_ == 0)
{
v___y_1623_ = v___y_1630_;
v___y_1624_ = v___y_1632_;
v_a_1625_ = v___x_1665_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1667_; size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1664_, v___x_1668_, v___x_1669_, v___x_1667_, v___y_1632_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_dec_ref_known(v___x_1670_, 1);
v___y_1623_ = v___y_1630_;
v___y_1624_ = v___y_1632_;
v_a_1625_ = v___x_1665_;
goto v___jp_1622_;
}
else
{
lean_dec(v___y_1630_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
return v___x_1670_;
}
}
}
else
{
lean_dec_ref(v___x_1641_);
v___y_1618_ = v___y_1630_;
v___y_1619_ = v___y_1632_;
goto v___jp_1617_;
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v_a_1671_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1673_ = v___x_1639_;
v_isShared_1674_ = v_isSharedCheck_1683_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1639_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1683_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1675_ = lean_io_error_to_string(v_a_1671_);
v___x_1676_ = 3;
v___x_1677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*1, v___x_1676_);
lean_inc_ref(v___y_1632_);
v___x_1678_ = lean_apply_2(v___y_1632_, v___x_1677_, lean_box(0));
v___x_1679_ = lean_box(0);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1679_);
v___x_1681_ = v___x_1673_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v_a_1684_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1686_ = v___x_1636_;
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1636_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1688_ = lean_io_error_to_string(v_a_1684_);
v___x_1689_ = 3;
v___x_1690_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*1, v___x_1689_);
lean_inc_ref(v___y_1632_);
v___x_1691_ = lean_apply_2(v___y_1632_, v___x_1690_, lean_box(0));
v___x_1692_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1692_);
v___x_1694_ = v___x_1686_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
v___jp_1697_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1700_);
v___x_1703_ = lean_apply_2(v___y_1700_, v___x_1702_, lean_box(0));
v___y_1629_ = v___y_1698_;
v___y_1630_ = v___y_1699_;
v___y_1631_ = v___y_1701_;
v___y_1632_ = v___y_1700_;
goto v___jp_1628_;
}
v___jp_1704_:
{
if (lean_obj_tag(v___y_1709_) == 0)
{
lean_dec_ref_known(v___y_1709_, 1);
v___y_1629_ = v___y_1705_;
v___y_1630_ = v___y_1706_;
v___y_1631_ = v___y_1708_;
v___y_1632_ = v___y_1707_;
goto v___jp_1628_;
}
else
{
lean_dec_ref_known(v___y_1709_, 1);
v___y_1698_ = v___y_1705_;
v___y_1699_ = v___y_1706_;
v___y_1700_ = v___y_1707_;
v___y_1701_ = v___y_1708_;
goto v___jp_1697_;
}
}
v___jp_1710_:
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = l_Lake_Git_upstreamBranch;
v___x_1716_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1586_);
v___x_1719_ = l_Lake_GitRepo_checkoutBranch(v___x_1715_, v_dir_1586_, v___x_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 1);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 2);
v___x_1721_ = lean_array_get_size(v_a_1720_);
v___x_1722_ = lean_nat_dec_lt(v___x_1717_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec(v_a_1720_);
v___y_1629_ = v___y_1711_;
v___y_1630_ = v___y_1712_;
v___y_1631_ = v___y_1714_;
v___y_1632_ = v___y_1713_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = lean_usize_of_nat(v___x_1721_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1720_, v___x_1724_, v___x_1725_, v___x_1723_, v___y_1713_);
lean_dec(v_a_1720_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_dec_ref_known(v___x_1726_, 1);
v___y_1629_ = v___y_1711_;
v___y_1630_ = v___y_1712_;
v___y_1631_ = v___y_1714_;
v___y_1632_ = v___y_1713_;
goto v___jp_1628_;
}
else
{
v___y_1705_ = v___y_1711_;
v___y_1706_ = v___y_1712_;
v___y_1707_ = v___y_1713_;
v___y_1708_ = v___y_1714_;
v___y_1709_ = v___x_1726_;
goto v___jp_1704_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1719_, 1);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1719_, 2);
v___x_1728_ = lean_array_get_size(v_a_1727_);
v___x_1729_ = lean_nat_dec_lt(v___x_1717_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec(v_a_1727_);
v___y_1698_ = v___y_1711_;
v___y_1699_ = v___y_1712_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1714_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = lean_usize_of_nat(v___x_1728_);
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1727_, v___x_1731_, v___x_1732_, v___x_1730_, v___y_1713_);
lean_dec(v_a_1727_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref_known(v___x_1733_, 1);
v___y_1698_ = v___y_1711_;
v___y_1699_ = v___y_1712_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1714_;
goto v___jp_1697_;
}
else
{
v___y_1705_ = v___y_1711_;
v___y_1706_ = v___y_1712_;
v___y_1707_ = v___y_1713_;
v___y_1708_ = v___y_1714_;
v___y_1709_ = v___x_1733_;
goto v___jp_1704_;
}
}
}
}
else
{
v___y_1629_ = v___y_1711_;
v___y_1630_ = v___y_1712_;
v___y_1631_ = v___y_1714_;
v___y_1632_ = v___y_1713_;
goto v___jp_1628_;
}
}
v___jp_1734_:
{
if (lean_obj_tag(v___y_1739_) == 0)
{
lean_dec_ref_known(v___y_1739_, 1);
v___y_1711_ = v___y_1735_;
v___y_1712_ = v___y_1736_;
v___y_1713_ = v___y_1737_;
v___y_1714_ = v___y_1738_;
goto v___jp_1710_;
}
else
{
lean_dec_ref_known(v___y_1739_, 1);
v___y_1698_ = v___y_1735_;
v___y_1699_ = v___y_1736_;
v___y_1700_ = v___y_1737_;
v___y_1701_ = v___y_1738_;
goto v___jp_1697_;
}
}
v___jp_1740_:
{
if (v_a_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1586_);
v___x_1748_ = l_Lake_GitRepo_quietInit(v_dir_1586_, v___x_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 2);
v___x_1750_ = lean_array_get_size(v_a_1749_);
v___x_1751_ = lean_nat_dec_lt(v___x_1746_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec(v_a_1749_);
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1742_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1752_; size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = lean_usize_of_nat(v___x_1750_);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1749_, v___x_1753_, v___x_1754_, v___x_1752_, v___y_1743_);
lean_dec(v_a_1749_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref_known(v___x_1755_, 1);
v___y_1711_ = v___y_1741_;
v___y_1712_ = v___y_1742_;
v___y_1713_ = v___y_1743_;
v___y_1714_ = v___y_1744_;
goto v___jp_1710_;
}
else
{
v___y_1735_ = v___y_1741_;
v___y_1736_ = v___y_1742_;
v___y_1737_ = v___y_1743_;
v___y_1738_ = v___y_1744_;
v___y_1739_ = v___x_1755_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1748_, 2);
v___x_1757_ = lean_array_get_size(v_a_1756_);
v___x_1758_ = lean_nat_dec_lt(v___x_1746_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec(v_a_1756_);
v___y_1698_ = v___y_1741_;
v___y_1699_ = v___y_1742_;
v___y_1700_ = v___y_1743_;
v___y_1701_ = v___y_1744_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1759_ = lean_box(0);
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1757_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1756_, v___x_1760_, v___x_1761_, v___x_1759_, v___y_1743_);
lean_dec(v_a_1756_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_dec_ref_known(v___x_1762_, 1);
v___y_1698_ = v___y_1741_;
v___y_1699_ = v___y_1742_;
v___y_1700_ = v___y_1743_;
v___y_1701_ = v___y_1744_;
goto v___jp_1697_;
}
else
{
v___y_1735_ = v___y_1741_;
v___y_1736_ = v___y_1742_;
v___y_1737_ = v___y_1743_;
v___y_1738_ = v___y_1744_;
v___y_1739_ = v___x_1762_;
goto v___jp_1734_;
}
}
}
}
else
{
v___y_1629_ = v___y_1741_;
v___y_1630_ = v___y_1742_;
v___y_1631_ = v___y_1744_;
v___y_1632_ = v___y_1743_;
goto v___jp_1628_;
}
}
v___jp_1763_:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1586_);
v___x_1769_ = l_Lake_GitRepo_insideWorkTree(v_dir_1586_);
v___x_1770_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1770_ == 0)
{
v___y_1741_ = v___y_1764_;
v___y_1742_ = v___y_1765_;
v___y_1743_ = v___y_1767_;
v___y_1744_ = v___y_1766_;
v_a_1745_ = v___x_1769_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1768_, v___x_1772_, v___x_1773_, v___x_1771_, v___y_1767_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_dec_ref_known(v___x_1774_, 1);
v___y_1741_ = v___y_1764_;
v___y_1742_ = v___y_1765_;
v___y_1743_ = v___y_1767_;
v___y_1744_ = v___y_1766_;
v_a_1745_ = v___x_1769_;
goto v___jp_1740_;
}
else
{
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
return v___x_1774_;
}
}
}
v___jp_1775_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_IO_FS_writeFile(v___y_1778_, v___y_1781_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___y_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_dec_ref_known(v___x_1782_, 1);
v___y_1764_ = v___y_1776_;
v___y_1765_ = v___y_1777_;
v___y_1766_ = v___y_1779_;
v___y_1767_ = v___y_1780_;
goto v___jp_1763_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_env_1590_);
lean_dec_ref(v_dir_1586_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1787_ = lean_io_error_to_string(v_a_1783_);
v___x_1788_ = 3;
v___x_1789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*1, v___x_1788_);
lean_inc_ref(v___y_1780_);
v___x_1790_ = lean_apply_2(v___y_1780_, v___x_1789_, lean_box(0));
v___x_1791_ = lean_box(0);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1791_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
v___jp_1796_:
{
if (v_a_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1803_ = lean_box(v_tmp_1588_);
v___x_1804_ = lean_obj_tag_nat(v___x_1803_);
lean_dec(v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(4u);
v___x_1806_ = lean_nat_dec_eq(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1587_);
v___x_1808_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1807_);
lean_dec_ref(v___x_1807_);
v___y_1776_ = v___y_1797_;
v___y_1777_ = v___y_1798_;
v___y_1778_ = v___y_1799_;
v___y_1779_ = v___y_1800_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___x_1808_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1587_);
v___x_1810_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1809_);
lean_dec_ref(v___x_1809_);
v___y_1776_ = v___y_1797_;
v___y_1777_ = v___y_1798_;
v___y_1778_ = v___y_1799_;
v___y_1779_ = v___y_1800_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___x_1810_;
goto v___jp_1775_;
}
}
else
{
lean_dec_ref(v___y_1799_);
lean_dec(v_name_1587_);
v___y_1764_ = v___y_1797_;
v___y_1765_ = v___y_1798_;
v___y_1766_ = v___y_1800_;
v___y_1767_ = v___y_1801_;
goto v___jp_1763_;
}
}
v___jp_1811_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1816_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_1586_);
v___x_1817_ = l_Lake_joinRelative(v_dir_1586_, v___x_1816_);
v___x_1818_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1819_ = l_System_FilePath_pathExists(v___x_1817_);
v___x_1820_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1820_ == 0)
{
v___y_1797_ = v___y_1812_;
v___y_1798_ = v___y_1813_;
v___y_1799_ = v___x_1817_;
v___y_1800_ = v___y_1814_;
v___y_1801_ = v___y_1815_;
v_a_1802_ = v___x_1819_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1818_, v___x_1822_, v___x_1823_, v___x_1821_, v___y_1815_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_dec_ref_known(v___x_1824_, 1);
v___y_1797_ = v___y_1812_;
v___y_1798_ = v___y_1813_;
v___y_1799_ = v___x_1817_;
v___y_1800_ = v___y_1814_;
v___y_1801_ = v___y_1815_;
v_a_1802_ = v___x_1819_;
goto v___jp_1796_;
}
else
{
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_1824_;
}
}
}
v___jp_1825_:
{
if (v_a_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1833_ = lean_box(v_tmp_1588_);
v___x_1834_ = lean_obj_tag_nat(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_dec_eq(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1831_);
v___x_1838_ = l_IO_FS_writeFile(v___y_1828_, v___x_1837_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___y_1828_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref_known(v___x_1838_, 1);
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1830_;
v___y_1815_ = v___y_1829_;
goto v___jp_1811_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1851_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1843_ = lean_io_error_to_string(v_a_1839_);
v___x_1844_ = 3;
v___x_1845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*1, v___x_1844_);
lean_inc_ref(v___y_1829_);
v___x_1846_ = lean_apply_2(v___y_1829_, v___x_1845_, lean_box(0));
v___x_1847_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1847_);
v___x_1849_ = v___x_1841_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v___y_1831_);
v___x_1852_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1853_ = l_IO_FS_writeFile(v___y_1828_, v___x_1852_);
lean_dec_ref(v___y_1828_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_dec_ref_known(v___x_1853_, 1);
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1830_;
v___y_1815_ = v___y_1829_;
goto v___jp_1811_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1866_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1866_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1858_ = lean_io_error_to_string(v_a_1854_);
v___x_1859_ = 3;
v___x_1860_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*1, v___x_1859_);
lean_inc_ref(v___y_1829_);
v___x_1861_ = lean_apply_2(v___y_1829_, v___x_1860_, lean_box(0));
v___x_1862_ = lean_box(0);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1862_);
v___x_1864_ = v___x_1856_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1828_);
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1830_;
v___y_1815_ = v___y_1829_;
goto v___jp_1811_;
}
}
v___jp_1867_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1873_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1586_);
v___x_1874_ = l_Lake_joinRelative(v_dir_1586_, v___x_1873_);
v___x_1875_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1876_ = l_System_FilePath_pathExists(v___x_1874_);
v___x_1877_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1877_ == 0)
{
v___y_1826_ = v___y_1868_;
v___y_1827_ = v___y_1869_;
v___y_1828_ = v___x_1874_;
v___y_1829_ = v___y_1870_;
v___y_1830_ = v___y_1871_;
v___y_1831_ = v___y_1872_;
v_a_1832_ = v___x_1876_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = lean_box(0);
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1875_, v___x_1879_, v___x_1880_, v___x_1878_, v___y_1870_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_dec_ref_known(v___x_1881_, 1);
v___y_1826_ = v___y_1868_;
v___y_1827_ = v___y_1869_;
v___y_1828_ = v___x_1874_;
v___y_1829_ = v___y_1870_;
v___y_1830_ = v___y_1871_;
v___y_1831_ = v___y_1872_;
v_a_1832_ = v___x_1876_;
goto v___jp_1825_;
}
else
{
lean_dec_ref(v___x_1874_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_1881_;
}
}
}
v___jp_1882_:
{
switch(v_tmp_1588_)
{
case 0:
{
v___y_1868_ = v___y_1883_;
v___y_1869_ = v___y_1884_;
v___y_1870_ = v___y_1887_;
v___y_1871_ = v___y_1885_;
v___y_1872_ = v___y_1886_;
goto v___jp_1867_;
}
case 1:
{
v___y_1868_ = v___y_1883_;
v___y_1869_ = v___y_1884_;
v___y_1870_ = v___y_1887_;
v___y_1871_ = v___y_1885_;
v___y_1872_ = v___y_1886_;
goto v___jp_1867_;
}
default: 
{
lean_dec(v___y_1886_);
v___y_1812_ = v___y_1883_;
v___y_1813_ = v___y_1884_;
v___y_1814_ = v___y_1885_;
v___y_1815_ = v___y_1887_;
goto v___jp_1811_;
}
}
}
v___jp_1888_:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_IO_FS_writeFile(v___y_1890_, v___y_1895_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v___y_1890_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_dec_ref_known(v___x_1896_, 1);
v___y_1883_ = v___y_1889_;
v___y_1884_ = v___y_1891_;
v___y_1885_ = v___y_1892_;
v___y_1886_ = v___y_1894_;
v___y_1887_ = v___y_1893_;
goto v___jp_1882_;
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1901_ = lean_io_error_to_string(v_a_1897_);
v___x_1902_ = 3;
v___x_1903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*1, v___x_1902_);
lean_inc_ref(v___y_1893_);
v___x_1904_ = lean_apply_2(v___y_1893_, v___x_1903_, lean_box(0));
v___x_1905_ = lean_box(0);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1905_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
v___jp_1910_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1917_ = lean_box(v_tmp_1588_);
v___x_1918_ = lean_obj_tag_nat(v___x_1917_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_unsigned_to_nat(4u);
v___x_1920_ = lean_nat_dec_eq(v___x_1918_, v___x_1919_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = 1;
lean_inc_n(v___y_1915_, 2);
v___x_1922_ = l_Lean_Name_toString(v___y_1915_, v___x_1921_);
v___x_1923_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1922_, v___y_1915_);
lean_dec_ref(v___x_1922_);
v___y_1889_ = v___y_1911_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1913_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1915_;
v___y_1895_ = v___x_1923_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1924_; 
lean_inc(v___y_1915_);
v___x_1924_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1915_);
v___y_1889_ = v___y_1911_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1913_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___y_1915_;
v___y_1895_ = v___x_1924_;
goto v___jp_1888_;
}
}
v___jp_1925_:
{
if (v_a_1933_ == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_IO_FS_createDirAll(v___y_1931_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref_known(v___x_1934_, 1);
v___x_1935_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1936_ = l_IO_FS_writeFile(v___y_1928_, v___x_1935_);
lean_dec_ref(v___y_1928_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1911_ = v___y_1926_;
v___y_1912_ = v___y_1927_;
v___y_1913_ = v___y_1929_;
v___y_1914_ = v___y_1930_;
v___y_1915_ = v___y_1932_;
v___y_1916_ = v_a_1585_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1941_ = lean_io_error_to_string(v_a_1937_);
v___x_1942_ = 3;
v___x_1943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*1, v___x_1942_);
lean_inc_ref(v_a_1585_);
v___x_1944_ = lean_apply_2(v_a_1585_, v___x_1943_, lean_box(0));
v___x_1945_ = lean_box(0);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1945_);
v___x_1947_ = v___x_1939_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1950_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1952_ = v___x_1934_;
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1934_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1954_ = lean_io_error_to_string(v_a_1950_);
v___x_1955_ = 3;
v___x_1956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*1, v___x_1955_);
lean_inc_ref(v_a_1585_);
v___x_1957_ = lean_apply_2(v_a_1585_, v___x_1956_, lean_box(0));
v___x_1958_ = lean_box(0);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1958_);
v___x_1960_ = v___x_1952_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_dec_ref(v___y_1931_);
lean_dec_ref(v___y_1928_);
v___y_1911_ = v___y_1926_;
v___y_1912_ = v___y_1927_;
v___y_1913_ = v___y_1929_;
v___y_1914_ = v___y_1930_;
v___y_1915_ = v___y_1932_;
v___y_1916_ = v_a_1585_;
goto v___jp_1910_;
}
}
v___jp_1966_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_inc(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc(v_name_1587_);
v___x_1972_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1588_, v_lang_1589_, v_name_1587_, v___y_1970_, v___y_1971_);
v___x_1973_ = l_IO_FS_writeFile(v_configFile_1965_, v___x_1972_);
lean_dec_ref(v___x_1972_);
lean_dec_ref(v_configFile_1965_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref_known(v___x_1973_, 1);
if (lean_obj_tag(v___y_1968_) == 1)
{
lean_object* v_val_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; uint8_t v___x_1981_; 
v_val_1974_ = lean_ctor_get(v___y_1968_, 0);
lean_inc_n(v_val_1974_, 2);
lean_dec_ref_known(v___y_1968_, 1);
v___x_1975_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1976_ = l_System_FilePath_withExtension(v_val_1974_, v___x_1975_);
v___x_1977_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1976_);
v___x_1978_ = l_Lake_joinRelative(v___x_1976_, v___x_1977_);
v___x_1979_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1980_ = l_System_FilePath_pathExists(v___x_1978_);
v___x_1981_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1981_ == 0)
{
v___y_1926_ = v___y_1967_;
v___y_1927_ = v_val_1974_;
v___y_1928_ = v___x_1978_;
v___y_1929_ = v___y_1971_;
v___y_1930_ = v___y_1969_;
v___y_1931_ = v___x_1976_;
v___y_1932_ = v___y_1970_;
v_a_1933_ = v___x_1980_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1979_, v___x_1983_, v___x_1984_, v___x_1982_, v_a_1585_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_dec_ref_known(v___x_1985_, 1);
v___y_1926_ = v___y_1967_;
v___y_1927_ = v_val_1974_;
v___y_1928_ = v___x_1978_;
v___y_1929_ = v___y_1971_;
v___y_1930_ = v___y_1969_;
v___y_1931_ = v___x_1976_;
v___y_1932_ = v___y_1970_;
v_a_1933_ = v___x_1980_;
goto v___jp_1925_;
}
else
{
lean_dec_ref(v___x_1978_);
lean_dec_ref(v___x_1976_);
lean_dec(v_val_1974_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_1985_;
}
}
}
else
{
lean_dec(v___y_1968_);
v___y_1883_ = v___y_1967_;
v___y_1884_ = v___y_1971_;
v___y_1885_ = v___y_1969_;
v___y_1886_ = v___y_1970_;
v___y_1887_ = v_a_1585_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_a_1986_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1988_ = v___x_1973_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1973_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1990_ = lean_io_error_to_string(v_a_1986_);
v___x_1991_ = 3;
v___x_1992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*1, v___x_1991_);
lean_inc_ref(v_a_1585_);
v___x_1993_ = lean_apply_2(v_a_1585_, v___x_1992_, lean_box(0));
v___x_1994_ = lean_box(0);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1994_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
v___jp_1999_:
{
lean_object* v_lean_2002_; lean_object* v_toolchain_2003_; lean_object* v___x_2004_; 
v_lean_2002_ = lean_ctor_get(v_env_1590_, 1);
v_toolchain_2003_ = lean_ctor_get(v_env_1590_, 19);
lean_inc_ref(v_toolchain_2003_);
v___x_2004_ = l_Lake_ToolchainVer_ofString(v_toolchain_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_ver_2005_; lean_object* v___x_2006_; 
v_ver_2005_ = lean_ctor_get(v___x_2004_, 1);
lean_inc_ref(v_ver_2005_);
lean_dec_ref_known(v___x_2004_, 2);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_ver_2005_);
lean_inc_ref(v_toolchain_2003_);
lean_inc_ref(v_lean_2002_);
v___y_1967_ = v_lean_2002_;
v___y_1968_ = v_snd_2001_;
v___y_1969_ = v_toolchain_2003_;
v___y_1970_ = v_fst_2000_;
v___y_1971_ = v___x_2006_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_2007_; 
lean_dec_ref(v___x_2004_);
v___x_2007_ = lean_box(0);
lean_inc_ref(v_toolchain_2003_);
lean_inc_ref(v_lean_2002_);
v___y_1967_ = v_lean_2002_;
v___y_1968_ = v_snd_2001_;
v___y_1969_ = v_toolchain_2003_;
v___y_1970_ = v_fst_2000_;
v___y_1971_ = v___x_2007_;
goto v___jp_1966_;
}
}
v___jp_2008_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(0);
lean_inc(v_name_1587_);
v_fst_2000_ = v_name_1587_;
v_snd_2001_ = v___x_2009_;
goto v___jp_1999_;
}
v___jp_2010_:
{
if (v_a_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___y_2011_);
v_fst_2000_ = v___y_2012_;
v_snd_2001_ = v___x_2014_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref(v___y_2011_);
v___x_2015_ = lean_box(0);
v_fst_2000_ = v___y_2012_;
v_snd_2001_ = v___x_2015_;
goto v___jp_1999_;
}
}
v___jp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2019_ = lean_box(v_tmp_1588_);
v___x_2020_ = lean_obj_tag_nat(v___x_2019_);
lean_dec(v___x_2019_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = lean_nat_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
if (v_a_2018_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; uint8_t v___x_2027_; 
lean_inc(v_name_1587_);
v___x_2023_ = l_Lake_toUpperCamelCase(v_name_1587_);
lean_inc(v___x_2023_);
v___x_2024_ = l_Lean_modToFilePath(v_dir_1586_, v___x_2023_, v___y_2017_);
v___x_2025_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2026_ = l_System_FilePath_pathExists(v___x_2024_);
v___x_2027_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2027_ == 0)
{
v___y_2011_ = v___x_2024_;
v___y_2012_ = v___x_2023_;
v_a_2013_ = v___x_2026_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2025_, v___x_2029_, v___x_2030_, v___x_2028_, v_a_1585_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref_known(v___x_2031_, 1);
v___y_2011_ = v___x_2024_;
v___y_2012_ = v___x_2023_;
v_a_2013_ = v___x_2026_;
goto v___jp_2010_;
}
else
{
lean_dec_ref(v___x_2024_);
lean_dec(v___x_2023_);
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_2031_;
}
}
}
else
{
goto v___jp_2008_;
}
}
else
{
goto v___jp_2008_;
}
}
v___jp_2032_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2033_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_1587_);
v___x_2034_ = l_Lean_modToFilePath(v_dir_1586_, v_name_1587_, v___x_2033_);
v___x_2035_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2036_ = l_System_FilePath_pathExists(v___x_2034_);
lean_dec_ref(v___x_2034_);
v___x_2037_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2037_ == 0)
{
v___y_2017_ = v___x_2033_;
v_a_2018_ = v___x_2036_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = lean_box(0);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2035_, v___x_2039_, v___x_2040_, v___x_2038_, v_a_1585_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
v___y_2017_ = v___x_2033_;
v_a_2018_ = v___x_2036_;
goto v___jp_2016_;
}
else
{
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___x_2041_;
}
}
}
v___jp_2042_:
{
if (lean_obj_tag(v___y_2043_) == 0)
{
lean_dec_ref_known(v___y_2043_, 1);
goto v___jp_2032_;
}
else
{
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
return v___y_2043_;
}
}
v___jp_2044_:
{
if (v_a_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1586_);
v___x_2048_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1586_, v_tmp_1588_, v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 2);
v___x_2050_ = lean_array_get_size(v_a_2049_);
v___x_2051_ = lean_nat_dec_lt(v___x_2046_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec(v_a_2049_);
goto v___jp_2032_;
}
else
{
lean_object* v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2050_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2049_, v___x_2053_, v___x_2054_, v___x_2052_, v_a_1585_);
lean_dec(v_a_2049_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
goto v___jp_2032_;
}
else
{
v___y_2043_ = v___x_2055_;
goto v___jp_2042_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2048_, 2);
v___x_2057_ = lean_array_get_size(v_a_2056_);
v___x_2058_ = lean_nat_dec_lt(v___x_2046_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec(v_a_2056_);
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = lean_usize_of_nat(v___x_2057_);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2056_, v___x_2062_, v___x_2063_, v___x_2061_, v_a_1585_);
lean_dec(v_a_2056_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2072_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 1);
lean_ctor_set(v___x_2066_, 0, v___x_2061_);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2061_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
v___y_2043_ = v___x_2064_;
goto v___jp_2042_;
}
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref(v_configFile_1965_);
lean_dec_ref(v_env_1590_);
lean_dec(v_name_1587_);
lean_dec_ref(v_dir_1586_);
v___x_2073_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_1585_);
v___x_2074_ = lean_apply_2(v_a_1585_, v___x_2073_, lean_box(0));
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1585_ = stack[0].m_obj;
lean_object* v_dir_1586_ = stack[1].m_obj;
lean_object* v_name_1587_ = stack[2].m_obj;
uint8_t v_tmp_1588_ = stack[3].m_num;
uint8_t v_lang_1589_ = stack[4].m_num;
lean_object* v_env_1590_ = stack[5].m_obj;
uint8_t v_offline_1591_ = stack[6].m_num;
lean_object* v_res_2084_;
v_res_2084_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_1585_, v_dir_1586_, v_name_1587_, v_tmp_1588_, v_lang_1589_, v_env_1590_, v_offline_1591_);
stack->m_obj
 = v_res_2084_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2085_, lean_object* v_dir_2086_, lean_object* v_name_2087_, lean_object* v_tmp_2088_, lean_object* v_lang_2089_, lean_object* v_env_2090_, lean_object* v_offline_2091_, lean_object* v_a_2092_){
_start:
{
uint8_t v_tmp_boxed_2093_; uint8_t v_lang_boxed_2094_; uint8_t v_offline_boxed_2095_; lean_object* v_res_2096_; 
v_tmp_boxed_2093_ = lean_unbox(v_tmp_2088_);
v_lang_boxed_2094_ = lean_unbox(v_lang_2089_);
v_offline_boxed_2095_ = lean_unbox(v_offline_2091_);
v_res_2096_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2085_, v_dir_2086_, v_name_2087_, v_tmp_boxed_2093_, v_lang_boxed_2094_, v_env_2090_, v_offline_boxed_2095_);
lean_dec_ref(v_a_2085_);
return v_res_2096_;
}
}
lean_object* l_Lake_init(lean_object* v_name_2098_, uint8_t v_tmp_2099_, uint8_t v_lang_2100_, lean_object* v_env_2101_, lean_object* v_cwd_2102_, uint8_t v_offline_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___y_2107_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_a_2128_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2164_ = lean_string_dec_eq(v_name_2098_, v___x_2163_);
if (v___x_2164_ == 0)
{
v_a_2128_ = v_name_2098_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2165_; 
lean_dec_ref(v_name_2098_);
lean_inc_ref(v_cwd_2102_);
v___x_2165_ = lean_io_realpath(v_cwd_2102_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2183_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2183_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2183_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; 
lean_inc(v_a_2166_);
v___x_2170_ = l_System_FilePath_fileName(v_a_2166_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
v___x_2171_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2172_ = lean_string_append(v___x_2171_, v_a_2166_);
lean_dec(v_a_2166_);
v___x_2173_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2174_ = lean_string_append(v___x_2172_, v___x_2173_);
v___x_2175_ = 3;
v___x_2176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*1, v___x_2175_);
lean_inc_ref(v_a_2104_);
v___x_2177_ = lean_apply_2(v_a_2104_, v___x_2176_, lean_box(0));
v___x_2178_ = lean_box(0);
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2178_);
v___x_2180_ = v___x_2168_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v_val_2182_; 
lean_del_object(v___x_2168_);
lean_dec(v_a_2166_);
v_val_2182_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v___x_2170_, 1);
v_a_2128_ = v_val_2182_;
goto v___jp_2127_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
v_a_2184_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2186_ = v___x_2165_;
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2165_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2188_ = lean_io_error_to_string(v_a_2184_);
v___x_2189_ = 3;
v___x_2190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2189_);
lean_inc_ref(v_a_2104_);
v___x_2191_ = lean_apply_2(v_a_2104_, v___x_2190_, lean_box(0));
v___x_2192_ = lean_box(0);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2192_);
v___x_2194_ = v___x_2186_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
v___jp_2106_:
{
lean_object* v___x_2108_; 
lean_inc_ref(v_cwd_2102_);
v___x_2108_ = l_IO_FS_createDirAll(v_cwd_2102_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec_ref_known(v___x_2108_, 1);
v___x_2109_ = l_Lake_stringToLegalOrSimpleName(v___y_2107_);
v___x_2110_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2104_, v_cwd_2102_, v___x_2109_, v_tmp_2099_, v_lang_2100_, v_env_2101_, v_offline_2103_);
return v___x_2110_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___y_2107_);
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
v_a_2111_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2113_ = v___x_2108_;
v_isShared_2114_ = v_isSharedCheck_2123_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2108_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2123_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2115_ = lean_io_error_to_string(v_a_2111_);
v___x_2116_ = 3;
v___x_2117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v___x_2116_);
lean_inc_ref(v_a_2104_);
v___x_2118_ = lean_apply_2(v_a_2104_, v___x_2117_, lean_box(0));
v___x_2119_ = lean_box(0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2119_);
v___x_2121_ = v___x_2113_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
v___jp_2124_:
{
if (lean_obj_tag(v___y_2126_) == 0)
{
lean_dec_ref_known(v___y_2126_, 1);
v___y_2107_ = v___y_2125_;
goto v___jp_2106_;
}
else
{
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
return v___y_2126_;
}
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v_str_2133_; lean_object* v_startInclusive_2134_; lean_object* v_endExclusive_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_string_utf8_byte_size(v_a_2128_);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v_a_2128_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2130_);
v___x_2132_ = l_String_Slice_trimAscii(v___x_2131_);
v_str_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc_ref(v_str_2133_);
v_startInclusive_2134_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_startInclusive_2134_);
v_endExclusive_2135_ = lean_ctor_get(v___x_2132_, 2);
lean_inc(v_endExclusive_2135_);
lean_dec_ref(v___x_2132_);
v___x_2136_ = lean_string_utf8_extract_fast(v_str_2133_, v_startInclusive_2134_, v_endExclusive_2135_);
lean_dec(v_endExclusive_2135_);
lean_dec(v_startInclusive_2134_);
lean_dec_ref(v_str_2133_);
v___x_2137_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2136_);
v___x_2138_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2136_, v___x_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 2);
v___x_2140_ = lean_array_get_size(v_a_2139_);
v___x_2141_ = lean_nat_dec_lt(v___x_2129_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_dec(v_a_2139_);
v___y_2107_ = v___x_2136_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2142_; size_t v___x_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = lean_usize_of_nat(v___x_2140_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2139_, v___x_2143_, v___x_2144_, v___x_2142_, v_a_2104_);
lean_dec(v_a_2139_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_dec_ref_known(v___x_2145_, 1);
v___y_2107_ = v___x_2136_;
goto v___jp_2106_;
}
else
{
v___y_2125_ = v___x_2136_;
v___y_2126_ = v___x_2145_;
goto v___jp_2124_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2138_, 2);
v___x_2147_ = lean_array_get_size(v_a_2146_);
v___x_2148_ = lean_nat_dec_lt(v___x_2129_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec(v_a_2146_);
lean_dec_ref(v___x_2136_);
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2151_ = lean_box(0);
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2147_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2146_, v___x_2152_, v___x_2153_, v___x_2151_, v_a_2104_);
lean_dec(v_a_2146_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___x_2136_);
lean_dec_ref(v_cwd_2102_);
lean_dec_ref(v_env_2101_);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2154_, 0);
lean_dec(v_unused_2162_);
v___x_2156_ = v___x_2154_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_dec(v___x_2154_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 1);
lean_ctor_set(v___x_2156_, 0, v___x_2151_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2151_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
v___y_2125_ = v___x_2136_;
v___y_2126_ = v___x_2154_;
goto v___jp_2124_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_init_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2098_ = stack[0].m_obj;
uint8_t v_tmp_2099_ = stack[1].m_num;
uint8_t v_lang_2100_ = stack[2].m_num;
lean_object* v_env_2101_ = stack[3].m_obj;
lean_object* v_cwd_2102_ = stack[4].m_obj;
uint8_t v_offline_2103_ = stack[5].m_num;
lean_object* v_a_2104_ = stack[6].m_obj;
lean_object* v_res_2197_;
v_res_2197_ = l_Lake_init(v_name_2098_, v_tmp_2099_, v_lang_2100_, v_env_2101_, v_cwd_2102_, v_offline_2103_, v_a_2104_);
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2198_, lean_object* v_tmp_2199_, lean_object* v_lang_2200_, lean_object* v_env_2201_, lean_object* v_cwd_2202_, lean_object* v_offline_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
uint8_t v_tmp_boxed_2206_; uint8_t v_lang_boxed_2207_; uint8_t v_offline_boxed_2208_; lean_object* v_res_2209_; 
v_tmp_boxed_2206_ = lean_unbox(v_tmp_2199_);
v_lang_boxed_2207_ = lean_unbox(v_lang_2200_);
v_offline_boxed_2208_ = lean_unbox(v_offline_2203_);
v_res_2209_ = l_Lake_init(v_name_2198_, v_tmp_boxed_2206_, v_lang_boxed_2207_, v_env_2201_, v_cwd_2202_, v_offline_boxed_2208_, v_a_2204_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
lean_object* l_Lake_new(lean_object* v_name_2210_, uint8_t v_tmp_2211_, uint8_t v_lang_2212_, lean_object* v_env_2213_, lean_object* v_cwd_2214_, uint8_t v_offline_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_str_2222_; lean_object* v_startInclusive_2223_; lean_object* v_endExclusive_2224_; lean_object* v_name_2225_; lean_object* v___y_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_string_utf8_byte_size(v_name_2210_);
v___x_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2220_, 0, v_name_2210_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
lean_ctor_set(v___x_2220_, 2, v___x_2219_);
v___x_2221_ = l_String_Slice_trimAscii(v___x_2220_);
v_str_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc_ref(v_str_2222_);
v_startInclusive_2223_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_startInclusive_2223_);
v_endExclusive_2224_ = lean_ctor_get(v___x_2221_, 2);
lean_inc(v_endExclusive_2224_);
lean_dec_ref(v___x_2221_);
v_name_2225_ = lean_string_utf8_extract_fast(v_str_2222_, v_startInclusive_2223_, v_endExclusive_2224_);
lean_dec(v_endExclusive_2224_);
lean_dec(v_startInclusive_2223_);
lean_dec_ref(v_str_2222_);
v___x_2247_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2225_);
v___x_2248_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2225_, v___x_2247_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 1);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 2);
v___x_2250_ = lean_array_get_size(v_a_2249_);
v___x_2251_ = lean_nat_dec_lt(v___x_2218_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_dec(v_a_2249_);
goto v___jp_2226_;
}
else
{
lean_object* v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = lean_usize_of_nat(v___x_2250_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2249_, v___x_2253_, v___x_2254_, v___x_2252_, v_a_2216_);
lean_dec(v_a_2249_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref_known(v___x_2255_, 1);
goto v___jp_2226_;
}
else
{
v___y_2246_ = v___x_2255_;
goto v___jp_2245_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_a_2256_ = lean_ctor_get(v___x_2248_, 1);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2248_, 2);
v___x_2257_ = lean_array_get_size(v_a_2256_);
v___x_2258_ = lean_nat_dec_lt(v___x_2218_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v_a_2256_);
lean_dec_ref(v_name_2225_);
lean_dec_ref(v_cwd_2214_);
lean_dec_ref(v_env_2213_);
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = lean_usize_of_nat(v___x_2257_);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2256_, v___x_2262_, v___x_2263_, v___x_2261_, v_a_2216_);
lean_dec(v_a_2256_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v_name_2225_);
lean_dec_ref(v_cwd_2214_);
lean_dec_ref(v_env_2213_);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v___x_2264_, 0);
lean_dec(v_unused_2272_);
v___x_2266_ = v___x_2264_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2264_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 1);
lean_ctor_set(v___x_2266_, 0, v___x_2261_);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2261_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
v___y_2246_ = v___x_2264_;
goto v___jp_2245_;
}
}
}
v___jp_2226_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = l_Lake_stringToLegalOrSimpleName(v_name_2225_);
lean_inc(v___x_2227_);
v___x_2228_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2227_);
v___x_2229_ = l_Lake_joinRelative(v_cwd_2214_, v___x_2228_);
lean_inc_ref(v___x_2229_);
v___x_2230_ = l_IO_FS_createDirAll(v___x_2229_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref_known(v___x_2230_, 1);
v___x_2231_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2216_, v___x_2229_, v___x_2227_, v_tmp_2211_, v_lang_2212_, v_env_2213_, v_offline_2215_);
return v___x_2231_;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v___x_2229_);
lean_dec(v___x_2227_);
lean_dec_ref(v_env_2213_);
v_a_2232_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2234_ = v___x_2230_;
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2230_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2236_ = lean_io_error_to_string(v_a_2232_);
v___x_2237_ = 3;
v___x_2238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1, v___x_2237_);
lean_inc_ref(v_a_2216_);
v___x_2239_ = lean_apply_2(v_a_2216_, v___x_2238_, lean_box(0));
v___x_2240_ = lean_box(0);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2240_);
v___x_2242_ = v___x_2234_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
v___jp_2245_:
{
if (lean_obj_tag(v___y_2246_) == 0)
{
lean_dec_ref_known(v___y_2246_, 1);
goto v___jp_2226_;
}
else
{
lean_dec_ref(v_name_2225_);
lean_dec_ref(v_cwd_2214_);
lean_dec_ref(v_env_2213_);
return v___y_2246_;
}
}
}
}
LEAN_EXPORT void l_Lake_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2210_ = stack[0].m_obj;
uint8_t v_tmp_2211_ = stack[1].m_num;
uint8_t v_lang_2212_ = stack[2].m_num;
lean_object* v_env_2213_ = stack[3].m_obj;
lean_object* v_cwd_2214_ = stack[4].m_obj;
uint8_t v_offline_2215_ = stack[5].m_num;
lean_object* v_a_2216_ = stack[6].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l_Lake_new(v_name_2210_, v_tmp_2211_, v_lang_2212_, v_env_2213_, v_cwd_2214_, v_offline_2215_, v_a_2216_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2274_, lean_object* v_tmp_2275_, lean_object* v_lang_2276_, lean_object* v_env_2277_, lean_object* v_cwd_2278_, lean_object* v_offline_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
uint8_t v_tmp_boxed_2282_; uint8_t v_lang_boxed_2283_; uint8_t v_offline_boxed_2284_; lean_object* v_res_2285_; 
v_tmp_boxed_2282_ = lean_unbox(v_tmp_2275_);
v_lang_boxed_2283_ = lean_unbox(v_lang_2276_);
v_offline_boxed_2284_ = lean_unbox(v_offline_2279_);
v_res_2285_ = l_Lake_new(v_name_2274_, v_tmp_boxed_2282_, v_lang_boxed_2283_, v_env_2277_, v_cwd_2278_, v_offline_boxed_2284_, v_a_2280_);
lean_dec_ref(v_a_2280_);
return v_res_2285_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents);
l___private_Lake_CLI_Init_0__Lake_mainFileName = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName);
l_Lake_instInhabitedInitTemplate = _init_l_Lake_instInhabitedInitTemplate();
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Init(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl(uint8_t v_x_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(v_x_332_);
v___x_334_ = lean_obj_tag_nat(v___x_333_);
lean_dec(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl___boxed(lean_object* v_x_335_){
_start:
{
uint8_t v_x_4__boxed_336_; lean_object* v_res_337_; 
v_x_4__boxed_336_ = lean_unbox(v_x_335_);
v_res_337_ = l_Lake_InitTemplate_ctorIdx___impl(v_x_4__boxed_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* v_k_338_){
_start:
{
lean_inc(v_k_338_);
return v_k_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_339_);
lean_dec(v_k_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* v_motive_341_, lean_object* v_ctorIdx_342_, uint8_t v_t_343_, lean_object* v_h_344_, lean_object* v_k_345_){
_start:
{
lean_inc(v_k_345_);
return v_k_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* v_motive_346_, lean_object* v_ctorIdx_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_k_350_){
_start:
{
uint8_t v_t_boxed_351_; lean_object* v_res_352_; 
v_t_boxed_351_ = lean_unbox(v_t_348_);
v_res_352_ = l_Lake_InitTemplate_ctorElim(v_motive_346_, v_ctorIdx_347_, v_t_boxed_351_, v_h_349_, v_k_350_);
lean_dec(v_k_350_);
lean_dec(v_ctorIdx_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* v_std_353_){
_start:
{
lean_inc(v_std_353_);
return v_std_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* v_std_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_InitTemplate_std_elim___redArg(v_std_354_);
lean_dec(v_std_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* v_motive_356_, uint8_t v_t_357_, lean_object* v_h_358_, lean_object* v_std_359_){
_start:
{
lean_inc(v_std_359_);
return v_std_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_std_363_){
_start:
{
uint8_t v_t_boxed_364_; lean_object* v_res_365_; 
v_t_boxed_364_ = lean_unbox(v_t_361_);
v_res_365_ = l_Lake_InitTemplate_std_elim(v_motive_360_, v_t_boxed_364_, v_h_362_, v_std_363_);
lean_dec(v_std_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* v_exe_366_){
_start:
{
lean_inc(v_exe_366_);
return v_exe_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* v_exe_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_367_);
lean_dec(v_exe_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* v_motive_369_, uint8_t v_t_370_, lean_object* v_h_371_, lean_object* v_exe_372_){
_start:
{
lean_inc(v_exe_372_);
return v_exe_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* v_motive_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_exe_376_){
_start:
{
uint8_t v_t_boxed_377_; lean_object* v_res_378_; 
v_t_boxed_377_ = lean_unbox(v_t_374_);
v_res_378_ = l_Lake_InitTemplate_exe_elim(v_motive_373_, v_t_boxed_377_, v_h_375_, v_exe_376_);
lean_dec(v_exe_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* v_lib_379_){
_start:
{
lean_inc(v_lib_379_);
return v_lib_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* v_lib_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_380_);
lean_dec(v_lib_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* v_motive_382_, uint8_t v_t_383_, lean_object* v_h_384_, lean_object* v_lib_385_){
_start:
{
lean_inc(v_lib_385_);
return v_lib_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_lib_389_){
_start:
{
uint8_t v_t_boxed_390_; lean_object* v_res_391_; 
v_t_boxed_390_ = lean_unbox(v_t_387_);
v_res_391_ = l_Lake_InitTemplate_lib_elim(v_motive_386_, v_t_boxed_390_, v_h_388_, v_lib_389_);
lean_dec(v_lib_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* v_mathLax_392_){
_start:
{
lean_inc(v_mathLax_392_);
return v_mathLax_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* v_mathLax_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_393_);
lean_dec(v_mathLax_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* v_motive_395_, uint8_t v_t_396_, lean_object* v_h_397_, lean_object* v_mathLax_398_){
_start:
{
lean_inc(v_mathLax_398_);
return v_mathLax_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_mathLax_402_){
_start:
{
uint8_t v_t_boxed_403_; lean_object* v_res_404_; 
v_t_boxed_403_ = lean_unbox(v_t_400_);
v_res_404_ = l_Lake_InitTemplate_mathLax_elim(v_motive_399_, v_t_boxed_403_, v_h_401_, v_mathLax_402_);
lean_dec(v_mathLax_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* v_math_405_){
_start:
{
lean_inc(v_math_405_);
return v_math_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* v_math_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lake_InitTemplate_math_elim___redArg(v_math_406_);
lean_dec(v_math_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* v_motive_408_, uint8_t v_t_409_, lean_object* v_h_410_, lean_object* v_math_411_){
_start:
{
lean_inc(v_math_411_);
return v_math_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_math_415_){
_start:
{
uint8_t v_t_boxed_416_; lean_object* v_res_417_; 
v_t_boxed_416_ = lean_unbox(v_t_413_);
v_res_417_ = l_Lake_InitTemplate_math_elim(v_motive_412_, v_t_boxed_416_, v_h_414_, v_math_415_);
lean_dec(v_math_415_);
return v_res_417_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(2u);
v___x_434_ = lean_nat_to_int(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_to_int(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t v_x_437_, lean_object* v_prec_438_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v___y_461_; lean_object* v___y_468_; 
switch(v_x_437_)
{
case 0:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1024u);
v___x_475_ = lean_nat_dec_le(v___x_474_, v_prec_438_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_440_ = v___x_476_;
goto v___jp_439_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_440_ = v___x_477_;
goto v___jp_439_;
}
}
case 1:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1024u);
v___x_479_ = lean_nat_dec_le(v___x_478_, v_prec_438_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_447_ = v___x_480_;
goto v___jp_446_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_447_ = v___x_481_;
goto v___jp_446_;
}
}
case 2:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1024u);
v___x_483_ = lean_nat_dec_le(v___x_482_, v_prec_438_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_454_ = v___x_484_;
goto v___jp_453_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_454_ = v___x_485_;
goto v___jp_453_;
}
}
case 3:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1024u);
v___x_487_ = lean_nat_dec_le(v___x_486_, v_prec_438_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_461_ = v___x_488_;
goto v___jp_460_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_461_ = v___x_489_;
goto v___jp_460_;
}
}
default: 
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1024u);
v___x_491_ = lean_nat_dec_le(v___x_490_, v_prec_438_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_468_ = v___x_492_;
goto v___jp_467_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_468_ = v___x_493_;
goto v___jp_467_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
lean_inc(v___y_440_);
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
v___x_444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = l_Repr_addAppParen(v___x_444_, v_prec_438_);
return v___x_445_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
lean_inc(v___y_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_438_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
lean_inc(v___y_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_438_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
lean_inc(v___y_461_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_438_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
lean_inc(v___y_468_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
v___x_473_ = l_Repr_addAppParen(v___x_472_, v_prec_438_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* v_x_494_, lean_object* v_prec_495_){
_start:
{
uint8_t v_x_279__boxed_496_; lean_object* v_res_497_; 
v_x_279__boxed_496_ = lean_unbox(v_x_494_);
v_res_497_ = l_Lake_instReprInitTemplate_repr(v_x_279__boxed_496_, v_prec_495_);
lean_dec(v_prec_495_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* v_n_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_dec_le(v_n_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(2u);
v___x_504_ = lean_nat_dec_le(v_n_500_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_nat_dec_le(v_n_500_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 4;
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = 3;
return v___x_508_;
}
}
else
{
uint8_t v___x_509_; 
v___x_509_ = 2;
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_nat_dec_le(v_n_500_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 1;
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* v_n_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Lake_InitTemplate_ofNat(v_n_514_);
lean_dec(v_n_514_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t v_x_517_, uint8_t v_y_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_519_ = lean_box(v_x_517_);
v___x_520_ = lean_obj_tag_nat(v___x_519_);
lean_dec(v___x_519_);
v___x_521_ = lean_box(v_y_518_);
v___x_522_ = lean_obj_tag_nat(v___x_521_);
lean_dec(v___x_521_);
v___x_523_ = lean_nat_dec_eq(v___x_520_, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* v_x_524_, lean_object* v_y_525_){
_start:
{
uint8_t v_x_23__boxed_526_; uint8_t v_y_24__boxed_527_; uint8_t v_res_528_; lean_object* v_r_529_; 
v_x_23__boxed_526_ = lean_unbox(v_x_524_);
v_y_24__boxed_527_ = lean_unbox(v_y_525_);
v_res_528_ = l_Lake_instDecidableEqInitTemplate(v_x_23__boxed_526_, v_y_24__boxed_527_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
v___x_553_ = lean_string_dec_eq(v_x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
v___x_555_ = lean_string_dec_eq(v_x_551_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
v___x_557_ = lean_string_dec_eq(v_x_551_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
v___x_559_ = lean_string_dec_eq(v_x_551_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
v___x_561_ = lean_string_dec_eq(v_x_551_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_InitTemplate_ofString_x3f(v_x_568_);
lean_dec_ref(v_x_568_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void){
_start:
{
uint32_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_idBeginEscape;
v___x_572_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_573_ = lean_string_push(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void){
_start:
{
uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_idEndEscape;
v___x_575_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_576_ = lean_string_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* v_id_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
v___x_579_ = lean_string_append(v___x_578_, v_id_577_);
v___x_580_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* v_id_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_582_);
lean_dec_ref(v_id_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* v_msg_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_586_ = lean_panic_fn_borrowed(v___x_585_, v_msg_584_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_591_ = lean_unsigned_to_nat(23u);
v___x_592_ = lean_unsigned_to_nat(350u);
v___x_593_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_594_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_595_ = l_mkPanicMessageWithDecl(v___x_594_, v___x_593_, v___x_592_, v___x_591_, v___x_590_);
return v___x_595_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_598_ = lean_unsigned_to_nat(23u);
v___x_599_ = lean_unsigned_to_nat(353u);
v___x_600_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_601_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_602_ = l_mkPanicMessageWithDecl(v___x_601_, v___x_600_, v___x_599_, v___x_598_, v___x_597_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 0:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
v___x_605_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_604_);
return v___x_605_;
}
case 1:
{
lean_object* v_pre_606_; 
v_pre_606_ = lean_ctor_get(v_x_603_, 0);
if (lean_obj_tag(v_pre_606_) == 0)
{
lean_object* v_str_607_; lean_object* v___x_608_; 
v_str_607_ = lean_ctor_get(v_x_603_, 1);
v___x_608_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_607_);
return v___x_608_;
}
else
{
lean_object* v_str_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_str_609_ = lean_ctor_get(v_x_603_, 1);
v___x_610_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_606_);
v___x_611_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_609_);
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
lean_dec_ref(v___x_613_);
return v___x_614_;
}
}
default: 
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
v___x_616_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_615_);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_617_);
lean_dec(v_x_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* v_s_619_, lean_object* v_p_620_){
_start:
{
lean_object* v___y_622_; lean_object* v___y_623_; uint32_t v___y_627_; lean_object* v___x_639_; uint8_t v_decide_640_; 
v___x_639_ = lean_string_utf8_byte_size(v_s_619_);
v_decide_640_ = lean_nat_dec_eq(v_p_620_, v___x_639_);
if (v_decide_640_ == 0)
{
uint32_t v___x_641_; uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_string_utf8_get_fast(v_s_619_, v_p_620_);
v___x_642_ = 46;
v___x_643_ = lean_uint32_dec_eq(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
else
{
uint32_t v___x_644_; 
v___x_644_ = 45;
v___y_627_ = v___x_644_;
goto v___jp_626_;
}
}
else
{
lean_dec(v_p_620_);
return v_s_619_;
}
v___jp_621_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_nat_add(v_p_620_, v___y_623_);
lean_dec(v_p_620_);
v_s_619_ = v___y_622_;
v_p_620_ = v___x_624_;
goto _start;
}
v___jp_626_:
{
lean_object* v___x_628_; uint32_t v___x_629_; uint8_t v___x_630_; 
lean_inc(v_p_620_);
v___x_628_ = lean_string_utf8_set(v_s_619_, v_p_620_, v___y_627_);
v___x_629_ = 127;
v___x_630_ = lean_uint32_dec_le(v___y_627_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 2047;
v___x_632_ = lean_uint32_dec_le(v___y_627_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 65535;
v___x_634_ = lean_uint32_dec_le(v___y_627_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_unsigned_to_nat(4u);
v___y_622_ = v___x_628_;
v___y_623_ = v___x_635_;
goto v___jp_621_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = lean_unsigned_to_nat(3u);
v___y_622_ = v___x_628_;
v___y_623_ = v___x_636_;
goto v___jp_621_;
}
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_unsigned_to_nat(2u);
v___y_622_ = v___x_628_;
v___y_623_ = v___x_637_;
goto v___jp_621_;
}
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___y_622_ = v___x_628_;
v___y_623_ = v___x_638_;
goto v___jp_621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* v_name_645_){
_start:
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = 0;
v___x_647_ = l_Lean_Name_toString(v_name_645_, v___x_646_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(v___x_647_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* v_s_650_, lean_object* v_p_651_){
_start:
{
lean_object* v___y_653_; lean_object* v___y_654_; uint32_t v___y_658_; lean_object* v___x_670_; uint8_t v_decide_671_; 
v___x_670_ = lean_string_utf8_byte_size(v_s_650_);
v_decide_671_ = lean_nat_dec_eq(v_p_651_, v___x_670_);
if (v_decide_671_ == 0)
{
uint32_t v___x_672_; uint32_t v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_string_utf8_get_fast(v_s_650_, v_p_651_);
v___x_673_ = 65;
v___x_674_ = lean_uint32_dec_le(v___x_673_, v___x_672_);
if (v___x_674_ == 0)
{
v___y_658_ = v___x_672_;
goto v___jp_657_;
}
else
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 90;
v___x_676_ = lean_uint32_dec_le(v___x_672_, v___x_675_);
if (v___x_676_ == 0)
{
v___y_658_ = v___x_672_;
goto v___jp_657_;
}
else
{
uint32_t v___x_677_; uint32_t v___x_678_; 
v___x_677_ = 32;
v___x_678_ = lean_uint32_add(v___x_672_, v___x_677_);
v___y_658_ = v___x_678_;
goto v___jp_657_;
}
}
}
else
{
lean_dec(v_p_651_);
return v_s_650_;
}
v___jp_652_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_nat_add(v_p_651_, v___y_654_);
lean_dec(v_p_651_);
v_s_650_ = v___y_653_;
v_p_651_ = v___x_655_;
goto _start;
}
v___jp_657_:
{
lean_object* v___x_659_; uint32_t v___x_660_; uint8_t v___x_661_; 
lean_inc(v_p_651_);
v___x_659_ = lean_string_utf8_set(v_s_650_, v_p_651_, v___y_658_);
v___x_660_ = 127;
v___x_661_ = lean_uint32_dec_le(v___y_658_, v___x_660_);
if (v___x_661_ == 0)
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 2047;
v___x_663_ = lean_uint32_dec_le(v___y_658_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 65535;
v___x_665_ = lean_uint32_dec_le(v___y_658_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_unsigned_to_nat(4u);
v___y_653_ = v___x_659_;
v___y_654_ = v___x_666_;
goto v___jp_652_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_unsigned_to_nat(3u);
v___y_653_ = v___x_659_;
v___y_654_ = v___x_667_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_668_; 
v___x_668_ = lean_unsigned_to_nat(2u);
v___y_653_ = v___x_659_;
v___y_654_ = v___x_668_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___y_653_ = v___x_659_;
v___y_654_ = v___x_669_;
goto v___jp_652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_681_, uint8_t v_lang_682_, lean_object* v_pkgName_683_, lean_object* v_root_684_, lean_object* v_leanVer_x3f_685_){
_start:
{
lean_object* v_pkgNameStr_686_; lean_object* v___y_688_; 
v_pkgNameStr_686_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_683_);
if (lean_obj_tag(v_leanVer_x3f_685_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_688_ = v___x_719_;
goto v___jp_687_;
}
else
{
lean_object* v_val_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_val_720_ = lean_ctor_get(v_leanVer_x3f_685_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_leanVer_x3f_685_, 1);
v___x_721_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_722_ = l_Lake_StdVer_toString(v_val_720_);
v___x_723_ = lean_string_append(v___x_721_, v___x_722_);
lean_dec_ref(v___x_722_);
v___y_688_ = v___x_723_;
goto v___jp_687_;
}
v___jp_687_:
{
switch(v_tmp_681_)
{
case 0:
{
lean_dec_ref(v___y_688_);
if (v_lang_682_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_684_);
lean_dec(v_root_684_);
v___x_690_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_686_);
v___x_691_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_686_, v___x_690_);
v___x_692_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_686_, v___x_689_, v___x_691_);
lean_dec_ref(v___x_689_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = 1;
v___x_694_ = l_Lean_Name_toString(v_root_684_, v___x_693_);
v___x_695_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_686_);
v___x_696_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_686_, v___x_695_);
v___x_697_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_686_, v___x_694_, v___x_696_);
return v___x_697_;
}
}
case 1:
{
lean_dec_ref(v___y_688_);
lean_dec(v_root_684_);
if (v_lang_682_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_686_);
v___x_699_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_686_, v___x_698_);
v___x_700_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_686_, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_686_);
v___x_702_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_686_, v___x_701_);
v___x_703_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_686_, v___x_702_);
return v___x_703_;
}
}
case 2:
{
lean_dec_ref(v___y_688_);
if (v_lang_682_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_684_);
lean_dec(v_root_684_);
v___x_705_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_686_, v___x_704_);
lean_dec_ref(v___x_704_);
return v___x_705_;
}
else
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = 1;
v___x_707_ = l_Lean_Name_toString(v_root_684_, v___x_706_);
v___x_708_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_686_, v___x_707_);
return v___x_708_;
}
}
case 3:
{
if (v_lang_682_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_684_);
lean_dec(v_root_684_);
v___x_710_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_686_, v___x_709_, v___y_688_);
lean_dec_ref(v___x_709_);
return v___x_710_;
}
else
{
uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = 1;
v___x_712_ = l_Lean_Name_toString(v_root_684_, v___x_711_);
v___x_713_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_686_, v___x_712_, v___y_688_);
return v___x_713_;
}
}
default: 
{
if (v_lang_682_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_684_);
lean_dec(v_root_684_);
v___x_715_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_686_, v___x_714_, v___y_688_);
lean_dec_ref(v___x_714_);
return v___x_715_;
}
else
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = 1;
v___x_717_ = l_Lean_Name_toString(v_root_684_, v___x_716_);
v___x_718_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_686_, v___x_717_, v___y_688_);
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_724_, lean_object* v_lang_725_, lean_object* v_pkgName_726_, lean_object* v_root_727_, lean_object* v_leanVer_x3f_728_){
_start:
{
uint8_t v_tmp_boxed_729_; uint8_t v_lang_boxed_730_; lean_object* v_res_731_; 
v_tmp_boxed_729_ = lean_unbox(v_tmp_724_);
v_lang_boxed_730_ = lean_unbox(v_lang_725_);
v_res_731_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_729_, v_lang_boxed_730_, v_pkgName_726_, v_root_727_, v_leanVer_x3f_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_757_, uint8_t v_tmp_758_, lean_object* v_a_759_){
_start:
{
uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_761_ = 0;
v___x_762_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_763_ = lean_array_push(v_a_759_, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_765_ = l_Lake_joinRelative(v_dir_757_, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_767_ = l_Lake_joinRelative(v___x_765_, v___x_766_);
lean_inc_ref(v___x_767_);
v___x_768_ = l_IO_FS_createDirAll(v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___y_772_; uint8_t v___x_829_; 
lean_dec_ref_known(v___x_768_, 1);
v___x_769_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_767_);
v___x_770_ = l_Lake_joinRelative(v___x_767_, v___x_769_);
v___x_829_ = l_System_FilePath_pathExists(v___x_770_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_830_ = lean_box(v_tmp_758_);
v___x_831_ = lean_obj_tag_nat(v___x_830_);
lean_dec(v___x_830_);
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_nat_dec_eq(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_835_ = l_IO_FS_writeFile(v___x_770_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec_ref_known(v___x_835_, 1);
v___y_772_ = v___x_763_;
goto v___jp_771_;
}
else
{
lean_object* v_a_836_; lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_767_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = lean_io_error_to_string(v_a_836_);
v___x_838_ = 3;
v___x_839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v___x_838_);
v___x_840_ = lean_array_get_size(v___x_763_);
v___x_841_ = lean_array_push(v___x_763_, v___x_839_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_844_ = l_IO_FS_writeFile(v___x_770_, v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_dec_ref_known(v___x_844_, 1);
v___y_772_ = v___x_763_;
goto v___jp_771_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_767_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = lean_io_error_to_string(v_a_845_);
v___x_847_ = 3;
v___x_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = lean_array_get_size(v___x_763_);
v___x_850_ = lean_array_push(v___x_763_, v___x_848_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
return v___x_851_;
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v___x_770_);
lean_dec_ref(v___x_767_);
v___x_852_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
v___x_853_ = lean_array_push(v___x_763_, v___x_852_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
return v___x_855_;
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_773_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_774_ = lean_string_append(v___x_773_, v___x_770_);
lean_dec_ref(v___x_770_);
v___x_775_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_761_);
v___x_778_ = lean_array_push(v___y_772_, v___x_777_);
v___x_779_ = lean_box(v_tmp_758_);
v___x_780_ = lean_obj_tag_nat(v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = lean_unsigned_to_nat(4u);
v___x_782_ = lean_nat_dec_eq(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v___x_767_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_778_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(v___x_767_);
v___x_786_ = l_Lake_joinRelative(v___x_767_, v___x_785_);
v___x_787_ = l_System_FilePath_pathExists(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_789_ = l_IO_FS_writeFile(v___x_786_, v___x_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
lean_dec_ref_known(v___x_789_, 1);
v___x_790_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
v___x_791_ = lean_string_append(v___x_790_, v___x_786_);
lean_dec_ref(v___x_786_);
v___x_792_ = lean_string_append(v___x_791_, v___x_775_);
v___x_793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*1, v___x_761_);
v___x_794_ = lean_array_push(v___x_778_, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_796_ = l_Lake_joinRelative(v___x_767_, v___x_795_);
v___x_797_ = l_System_FilePath_pathExists(v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_799_ = l_IO_FS_writeFile(v___x_796_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_801_ = lean_string_append(v___x_800_, v___x_796_);
lean_dec_ref(v___x_796_);
v___x_802_ = lean_string_append(v___x_801_, v___x_775_);
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_761_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_array_push(v___x_794_, v___x_803_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec_ref(v___x_796_);
v_a_807_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_799_, 1);
v___x_808_ = lean_io_error_to_string(v_a_807_);
v___x_809_ = 3;
v___x_810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*1, v___x_809_);
v___x_811_ = lean_array_get_size(v___x_794_);
v___x_812_ = lean_array_push(v___x_794_, v___x_810_);
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v___x_796_);
v___x_814_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
v___x_815_ = lean_array_push(v___x_794_, v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
return v___x_817_;
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_767_);
v_a_818_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_789_, 1);
v___x_819_ = lean_io_error_to_string(v_a_818_);
v___x_820_ = 3;
v___x_821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v___x_820_);
v___x_822_ = lean_array_get_size(v___x_778_);
v___x_823_ = lean_array_push(v___x_778_, v___x_821_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
return v___x_824_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_767_);
v___x_825_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
v___x_826_ = lean_array_push(v___x_778_, v___x_825_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v___x_767_);
v_a_856_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_768_, 1);
v___x_857_ = lean_io_error_to_string(v_a_856_);
v___x_858_ = 3;
v___x_859_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*1, v___x_858_);
v___x_860_ = lean_array_get_size(v___x_763_);
v___x_861_ = lean_array_push(v___x_763_, v___x_859_);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_863_, lean_object* v_tmp_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v_tmp_boxed_867_; lean_object* v_res_868_; 
v_tmp_boxed_867_ = lean_unbox(v_tmp_864_);
v_res_868_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_863_, v_tmp_boxed_867_, v_a_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_869_, size_t v_i_870_, size_t v_stop_871_, lean_object* v_b_872_, lean_object* v___y_873_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = lean_usize_dec_eq(v_i_870_, v_stop_871_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; size_t v___x_878_; size_t v___x_879_; 
v___x_876_ = lean_array_uget_borrowed(v_as_869_, v_i_870_);
lean_inc_ref(v___y_873_);
lean_inc(v___x_876_);
v___x_877_ = lean_apply_2(v___y_873_, v___x_876_, lean_box(0));
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_870_, v___x_878_);
v_i_870_ = v___x_879_;
v_b_872_ = v___x_877_;
goto _start;
}
else
{
lean_object* v___x_881_; 
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_b_872_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_882_, lean_object* v_i_883_, lean_object* v_stop_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v_i_boxed_888_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_884_);
lean_dec(v_stop_884_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_882_, v_i_boxed_888_, v_stop_boxed_889_, v_b_885_, v___y_886_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_as_882_);
return v_res_890_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_905_ = lean_array_get_size(v___x_904_);
return v___x_905_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_nat_dec_lt(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_909_; size_t v___x_910_; 
v___x_909_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_910_ = lean_usize_of_nat(v___x_909_);
return v___x_910_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_916_ = l_Lake_Git_upstreamBranch;
v___x_917_ = lean_string_dec_eq(v___x_916_, v___x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_925_, lean_object* v_name_926_, uint8_t v_tmp_927_, uint8_t v_lang_928_, lean_object* v_env_929_, uint8_t v_offline_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___y_935_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_963_; lean_object* v___y_964_; uint8_t v_a_965_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v_a_1073_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; uint8_t v_a_1130_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; uint8_t v_a_1160_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v_a_1261_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_configFile_1293_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___y_1339_; lean_object* v___y_1340_; uint8_t v_a_1341_; lean_object* v___y_1345_; uint8_t v_a_1346_; uint8_t v_a_1371_; lean_object* v___x_1403_; uint8_t v___x_1404_; uint8_t v___x_1405_; 
v___x_933_ = l_Lake_defaultConfigFile;
v___x_1291_ = l_Lake_ConfigLang_fileExtension(v_lang_928_);
v___x_1292_ = l_System_FilePath_addExtension(v___x_933_, v___x_1291_);
lean_dec_ref(v___x_1291_);
lean_inc_ref(v_dir_925_);
v_configFile_1293_ = l_Lake_joinRelative(v_dir_925_, v___x_1292_);
v___x_1403_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1404_ = l_System_FilePath_pathExists(v_configFile_1293_);
v___x_1405_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1405_ == 0)
{
v_a_1371_ = v___x_1404_;
goto v___jp_1370_;
}
else
{
lean_object* v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1403_, v___x_1407_, v___x_1408_, v___x_1406_, v_a_931_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec_ref_known(v___x_1409_, 1);
v_a_1371_ = v___x_1404_;
goto v___jp_1370_;
}
else
{
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1409_;
}
}
v___jp_934_:
{
if (v_offline_930_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_936_ = lean_box(0);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_box(0);
v___x_939_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_925_);
v___x_940_ = l_Lake_joinRelative(v_dir_925_, v___x_939_);
lean_inc_ref(v___x_940_);
v___x_941_ = l_Lake_joinRelative(v___x_940_, v___x_933_);
v___x_942_ = l_Lake_defaultManifestFile;
v___x_943_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_944_ = lean_box(1);
v___x_945_ = l_Lean_Options_empty;
v___x_946_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_947_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_947_, 0, v_env_929_);
lean_ctor_set(v___x_947_, 1, v___x_936_);
lean_ctor_set(v___x_947_, 2, v_dir_925_);
lean_ctor_set(v___x_947_, 3, v___x_937_);
lean_ctor_set(v___x_947_, 4, v___x_938_);
lean_ctor_set(v___x_947_, 5, v___x_939_);
lean_ctor_set(v___x_947_, 6, v___x_940_);
lean_ctor_set(v___x_947_, 7, v___x_933_);
lean_ctor_set(v___x_947_, 8, v___x_941_);
lean_ctor_set(v___x_947_, 9, v___x_936_);
lean_ctor_set(v___x_947_, 10, v___x_942_);
lean_ctor_set(v___x_947_, 11, v___x_943_);
lean_ctor_set(v___x_947_, 12, v___x_944_);
lean_ctor_set(v___x_947_, 13, v___x_945_);
lean_ctor_set(v___x_947_, 14, v___x_946_);
lean_ctor_set(v___x_947_, 15, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*16, v_offline_930_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*16 + 1, v_offline_930_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*16 + 2, v_offline_930_);
v___x_948_ = l_Lean_NameSet_empty;
v___x_949_ = l_Lake_updateManifest(v___x_947_, v___x_948_, v___y_935_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
v___jp_952_:
{
if (lean_obj_tag(v___y_954_) == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_953_);
v___x_956_ = lean_apply_2(v___y_953_, v___x_955_, lean_box(0));
v___y_935_ = v___y_953_;
goto v___jp_934_;
}
else
{
lean_dec_ref_known(v___y_954_, 1);
v___y_935_ = v___y_953_;
goto v___jp_934_;
}
}
v___jp_957_:
{
switch(v_tmp_927_)
{
case 3:
{
v___y_953_ = v___y_959_;
v___y_954_ = v___y_958_;
goto v___jp_952_;
}
case 4:
{
v___y_953_ = v___y_959_;
v___y_954_ = v___y_958_;
goto v___jp_952_;
}
default: 
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v___y_958_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
v___jp_962_:
{
if (v_a_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_963_);
v___x_967_ = lean_apply_2(v___y_963_, v___x_966_, lean_box(0));
v___y_958_ = v___y_964_;
v___y_959_ = v___y_963_;
goto v___jp_957_;
}
else
{
v___y_958_ = v___y_964_;
v___y_959_ = v___y_963_;
goto v___jp_957_;
}
}
v___jp_968_:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_925_);
v___x_974_ = l_Lake_joinRelative(v_dir_925_, v___x_973_);
v___x_975_ = 4;
v___x_976_ = lean_io_prim_handle_mk(v___x_974_, v___x_975_);
lean_dec_ref(v___x_974_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_979_ = lean_io_prim_handle_put_str(v_a_977_, v___x_978_);
lean_dec(v_a_977_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
lean_dec_ref_known(v___x_979_, 1);
v___x_980_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_925_);
v___x_981_ = l_Lake_joinRelative(v_dir_925_, v___x_980_);
v___x_982_ = lean_string_utf8_byte_size(v___y_969_);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_nat_dec_eq(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v___y_970_);
v___x_985_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_986_ = lean_string_append(v___y_969_, v___x_985_);
v___x_987_ = l_IO_FS_writeFile(v___x_981_, v___x_986_);
lean_dec_ref(v___x_986_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref_known(v___x_987_, 1);
v___y_958_ = v___y_971_;
v___y_959_ = v___y_972_;
goto v___jp_957_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___y_971_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1000_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1000_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_992_ = lean_io_error_to_string(v_a_988_);
v___x_993_ = 3;
v___x_994_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*1, v___x_993_);
lean_inc_ref(v___y_972_);
v___x_995_ = lean_apply_2(v___y_972_, v___x_994_, lean_box(0));
v___x_996_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_996_);
v___x_998_ = v___x_990_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_githash_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
lean_dec_ref(v___y_969_);
v_githash_1001_ = lean_ctor_get(v___y_970_, 1);
lean_inc_ref(v_githash_1001_);
lean_dec_ref(v___y_970_);
v___x_1002_ = lean_string_utf8_byte_size(v_githash_1001_);
lean_dec_ref(v_githash_1001_);
v___x_1003_ = lean_nat_dec_eq(v___x_1002_, v___x_983_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1005_ = l_System_FilePath_pathExists(v___x_981_);
lean_dec_ref(v___x_981_);
v___x_1006_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1006_ == 0)
{
v___y_963_ = v___y_972_;
v___y_964_ = v___y_971_;
v_a_965_ = v___x_1005_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1004_, v___x_1008_, v___x_1009_, v___x_1007_, v___y_972_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_dec_ref_known(v___x_1010_, 1);
v___y_963_ = v___y_972_;
v___y_964_ = v___y_971_;
v_a_965_ = v___x_1005_;
goto v___jp_962_;
}
else
{
lean_dec(v___y_971_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
return v___x_1010_;
}
}
}
else
{
lean_dec_ref(v___x_981_);
v___y_958_ = v___y_971_;
v___y_959_ = v___y_972_;
goto v___jp_957_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v_a_1011_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1013_ = v___x_979_;
v_isShared_1014_ = v_isSharedCheck_1023_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_979_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1023_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1015_ = lean_io_error_to_string(v_a_1011_);
v___x_1016_ = 3;
v___x_1017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_1016_);
lean_inc_ref(v___y_972_);
v___x_1018_ = lean_apply_2(v___y_972_, v___x_1017_, lean_box(0));
v___x_1019_ = lean_box(0);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1019_);
v___x_1021_ = v___x_1013_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v_a_1024_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1026_ = v___x_976_;
v_isShared_1027_ = v_isSharedCheck_1036_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_976_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1036_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1028_ = lean_io_error_to_string(v_a_1024_);
v___x_1029_ = 3;
v___x_1030_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1029_);
lean_inc_ref(v___y_972_);
v___x_1031_ = lean_apply_2(v___y_972_, v___x_1030_, lean_box(0));
v___x_1032_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1032_);
v___x_1034_ = v___x_1026_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
v___jp_1037_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1039_);
v___x_1043_ = lean_apply_2(v___y_1039_, v___x_1042_, lean_box(0));
v___y_969_ = v___y_1038_;
v___y_970_ = v___y_1040_;
v___y_971_ = v___y_1041_;
v___y_972_ = v___y_1039_;
goto v___jp_968_;
}
v___jp_1044_:
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = l_Lake_Git_upstreamBranch;
v___x_1050_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_925_);
v___x_1053_ = l_Lake_GitRepo_checkoutBranch(v___x_1049_, v_dir_925_, v___x_1052_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 2);
v___x_1055_ = lean_array_get_size(v_a_1054_);
v___x_1056_ = lean_nat_dec_lt(v___x_1051_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v_a_1054_);
v___y_969_ = v___y_1045_;
v___y_970_ = v___y_1047_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1046_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = lean_usize_of_nat(v___x_1055_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1054_, v___x_1058_, v___x_1059_, v___x_1057_, v___y_1046_);
lean_dec(v_a_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_dec_ref_known(v___x_1060_, 1);
v___y_969_ = v___y_1045_;
v___y_970_ = v___y_1047_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1046_;
goto v___jp_968_;
}
else
{
lean_dec_ref_known(v___x_1060_, 1);
v___y_1038_ = v___y_1045_;
v___y_1039_ = v___y_1046_;
v___y_1040_ = v___y_1047_;
v___y_1041_ = v___y_1048_;
goto v___jp_1037_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_a_1061_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1053_, 2);
v___x_1062_ = lean_array_get_size(v_a_1061_);
v___x_1063_ = lean_nat_dec_lt(v___x_1051_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec(v_a_1061_);
v___y_1038_ = v___y_1045_;
v___y_1039_ = v___y_1046_;
v___y_1040_ = v___y_1047_;
v___y_1041_ = v___y_1048_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1062_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1061_, v___x_1065_, v___x_1066_, v___x_1064_, v___y_1046_);
lean_dec(v_a_1061_);
lean_dec_ref(v___x_1067_);
v___y_1038_ = v___y_1045_;
v___y_1039_ = v___y_1046_;
v___y_1040_ = v___y_1047_;
v___y_1041_ = v___y_1048_;
goto v___jp_1037_;
}
}
}
else
{
v___y_969_ = v___y_1045_;
v___y_970_ = v___y_1047_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1046_;
goto v___jp_968_;
}
}
v___jp_1068_:
{
if (v_a_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_925_);
v___x_1076_ = l_Lake_GitRepo_quietInit(v_dir_925_, v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 2);
v___x_1078_ = lean_array_get_size(v_a_1077_);
v___x_1079_ = lean_nat_dec_lt(v___x_1074_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_a_1077_);
v___y_1045_ = v___y_1069_;
v___y_1046_ = v___y_1070_;
v___y_1047_ = v___y_1071_;
v___y_1048_ = v___y_1072_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1078_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1077_, v___x_1081_, v___x_1082_, v___x_1080_, v___y_1070_);
lean_dec(v_a_1077_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec_ref_known(v___x_1083_, 1);
v___y_1045_ = v___y_1069_;
v___y_1046_ = v___y_1070_;
v___y_1047_ = v___y_1071_;
v___y_1048_ = v___y_1072_;
goto v___jp_1044_;
}
else
{
lean_dec_ref_known(v___x_1083_, 1);
v___y_1038_ = v___y_1069_;
v___y_1039_ = v___y_1070_;
v___y_1040_ = v___y_1071_;
v___y_1041_ = v___y_1072_;
goto v___jp_1037_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1076_, 2);
v___x_1085_ = lean_array_get_size(v_a_1084_);
v___x_1086_ = lean_nat_dec_lt(v___x_1074_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec(v_a_1084_);
v___y_1038_ = v___y_1069_;
v___y_1039_ = v___y_1070_;
v___y_1040_ = v___y_1071_;
v___y_1041_ = v___y_1072_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1085_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1084_, v___x_1088_, v___x_1089_, v___x_1087_, v___y_1070_);
lean_dec(v_a_1084_);
lean_dec_ref(v___x_1090_);
v___y_1038_ = v___y_1069_;
v___y_1039_ = v___y_1070_;
v___y_1040_ = v___y_1071_;
v___y_1041_ = v___y_1072_;
goto v___jp_1037_;
}
}
}
else
{
v___y_969_ = v___y_1069_;
v___y_970_ = v___y_1071_;
v___y_971_ = v___y_1072_;
v___y_972_ = v___y_1070_;
goto v___jp_968_;
}
}
v___jp_1091_:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_925_);
v___x_1097_ = l_Lake_GitRepo_insideWorkTree(v_dir_925_);
v___x_1098_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1098_ == 0)
{
v___y_1069_ = v___y_1092_;
v___y_1070_ = v___y_1095_;
v___y_1071_ = v___y_1093_;
v___y_1072_ = v___y_1094_;
v_a_1073_ = v___x_1097_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = lean_box(0);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1096_, v___x_1100_, v___x_1101_, v___x_1099_, v___y_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec_ref_known(v___x_1102_, 1);
v___y_1069_ = v___y_1092_;
v___y_1070_ = v___y_1095_;
v___y_1071_ = v___y_1093_;
v___y_1072_ = v___y_1094_;
v_a_1073_ = v___x_1097_;
goto v___jp_1068_;
}
else
{
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
return v___x_1102_;
}
}
}
v___jp_1103_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_IO_FS_writeFile(v___y_1107_, v___y_1109_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___y_1107_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1092_ = v___y_1104_;
v___y_1093_ = v___y_1106_;
v___y_1094_ = v___y_1108_;
v___y_1095_ = v___y_1105_;
goto v___jp_1091_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___y_1104_);
lean_dec_ref(v_env_929_);
lean_dec_ref(v_dir_925_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1123_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1123_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1115_ = lean_io_error_to_string(v_a_1111_);
v___x_1116_ = 3;
v___x_1117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*1, v___x_1116_);
lean_inc_ref(v___y_1105_);
v___x_1118_ = lean_apply_2(v___y_1105_, v___x_1117_, lean_box(0));
v___x_1119_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1119_);
v___x_1121_ = v___x_1113_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
v___jp_1124_:
{
if (v_a_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1131_ = lean_box(v_tmp_927_);
v___x_1132_ = lean_obj_tag_nat(v___x_1131_);
lean_dec(v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_926_);
v___x_1136_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1135_);
lean_dec_ref(v___x_1135_);
v___y_1104_ = v___y_1125_;
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1127_;
v___y_1107_ = v___y_1128_;
v___y_1108_ = v___y_1129_;
v___y_1109_ = v___x_1136_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_926_);
v___x_1138_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1137_);
lean_dec_ref(v___x_1137_);
v___y_1104_ = v___y_1125_;
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1127_;
v___y_1107_ = v___y_1128_;
v___y_1108_ = v___y_1129_;
v___y_1109_ = v___x_1138_;
goto v___jp_1103_;
}
}
else
{
lean_dec_ref(v___y_1128_);
lean_dec(v_name_926_);
v___y_1092_ = v___y_1125_;
v___y_1093_ = v___y_1127_;
v___y_1094_ = v___y_1129_;
v___y_1095_ = v___y_1126_;
goto v___jp_1091_;
}
}
v___jp_1139_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1144_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_925_);
v___x_1145_ = l_Lake_joinRelative(v_dir_925_, v___x_1144_);
v___x_1146_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1147_ = l_System_FilePath_pathExists(v___x_1145_);
v___x_1148_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1148_ == 0)
{
v___y_1125_ = v___y_1140_;
v___y_1126_ = v___y_1143_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___x_1145_;
v___y_1129_ = v___y_1142_;
v_a_1130_ = v___x_1147_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1146_, v___x_1150_, v___x_1151_, v___x_1149_, v___y_1143_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_dec_ref_known(v___x_1152_, 1);
v___y_1125_ = v___y_1140_;
v___y_1126_ = v___y_1143_;
v___y_1127_ = v___y_1141_;
v___y_1128_ = v___x_1145_;
v___y_1129_ = v___y_1142_;
v_a_1130_ = v___x_1147_;
goto v___jp_1124_;
}
else
{
lean_dec_ref(v___x_1145_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1152_;
}
}
}
v___jp_1153_:
{
if (v_a_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1161_ = lean_box(v_tmp_927_);
v___x_1162_ = lean_obj_tag_nat(v___x_1161_);
lean_dec(v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_dec_eq(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1155_);
v___x_1166_ = l_IO_FS_writeFile(v___y_1159_, v___x_1165_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_dec_ref_known(v___x_1166_, 1);
v___y_1140_ = v___y_1154_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1158_;
v___y_1143_ = v___y_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1171_ = lean_io_error_to_string(v_a_1167_);
v___x_1172_ = 3;
v___x_1173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1, v___x_1172_);
lean_inc_ref(v___y_1156_);
v___x_1174_ = lean_apply_2(v___y_1156_, v___x_1173_, lean_box(0));
v___x_1175_ = lean_box(0);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1175_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v___y_1155_);
v___x_1180_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1181_ = l_IO_FS_writeFile(v___y_1159_, v___x_1180_);
lean_dec_ref(v___y_1159_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_dec_ref_known(v___x_1181_, 1);
v___y_1140_ = v___y_1154_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1158_;
v___y_1143_ = v___y_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1186_ = lean_io_error_to_string(v_a_1182_);
v___x_1187_ = 3;
v___x_1188_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*1, v___x_1187_);
lean_inc_ref(v___y_1156_);
v___x_1189_ = lean_apply_2(v___y_1156_, v___x_1188_, lean_box(0));
v___x_1190_ = lean_box(0);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1190_);
v___x_1192_ = v___x_1184_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1155_);
v___y_1140_ = v___y_1154_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1158_;
v___y_1143_ = v___y_1156_;
goto v___jp_1139_;
}
}
v___jp_1195_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1201_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_925_);
v___x_1202_ = l_Lake_joinRelative(v_dir_925_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1204_ = l_System_FilePath_pathExists(v___x_1202_);
v___x_1205_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1205_ == 0)
{
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1197_;
v___y_1156_ = v___y_1198_;
v___y_1157_ = v___y_1199_;
v___y_1158_ = v___y_1200_;
v___y_1159_ = v___x_1202_;
v_a_1160_ = v___x_1204_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1203_, v___x_1207_, v___x_1208_, v___x_1206_, v___y_1198_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref_known(v___x_1209_, 1);
v___y_1154_ = v___y_1196_;
v___y_1155_ = v___y_1197_;
v___y_1156_ = v___y_1198_;
v___y_1157_ = v___y_1199_;
v___y_1158_ = v___y_1200_;
v___y_1159_ = v___x_1202_;
v_a_1160_ = v___x_1204_;
goto v___jp_1153_;
}
else
{
lean_dec_ref(v___x_1202_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1209_;
}
}
}
v___jp_1210_:
{
switch(v_tmp_927_)
{
case 0:
{
v___y_1196_ = v___y_1211_;
v___y_1197_ = v___y_1212_;
v___y_1198_ = v___y_1215_;
v___y_1199_ = v___y_1213_;
v___y_1200_ = v___y_1214_;
goto v___jp_1195_;
}
case 1:
{
v___y_1196_ = v___y_1211_;
v___y_1197_ = v___y_1212_;
v___y_1198_ = v___y_1215_;
v___y_1199_ = v___y_1213_;
v___y_1200_ = v___y_1214_;
goto v___jp_1195_;
}
default: 
{
lean_dec(v___y_1212_);
v___y_1140_ = v___y_1211_;
v___y_1141_ = v___y_1213_;
v___y_1142_ = v___y_1214_;
v___y_1143_ = v___y_1215_;
goto v___jp_1139_;
}
}
}
v___jp_1216_:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_IO_FS_writeFile(v___y_1220_, v___y_1223_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1220_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec_ref_known(v___x_1224_, 1);
v___y_1211_ = v___y_1217_;
v___y_1212_ = v___y_1218_;
v___y_1213_ = v___y_1221_;
v___y_1214_ = v___y_1222_;
v___y_1215_ = v___y_1219_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1229_ = lean_io_error_to_string(v_a_1225_);
v___x_1230_ = 3;
v___x_1231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*1, v___x_1230_);
lean_inc_ref(v___y_1219_);
v___x_1232_ = lean_apply_2(v___y_1219_, v___x_1231_, lean_box(0));
v___x_1233_ = lean_box(0);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1233_);
v___x_1235_ = v___x_1227_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
v___jp_1238_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1245_ = lean_box(v_tmp_927_);
v___x_1246_ = lean_obj_tag_nat(v___x_1245_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(4u);
v___x_1248_ = lean_nat_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = 1;
lean_inc_n(v___y_1240_, 2);
v___x_1250_ = l_Lean_Name_toString(v___y_1240_, v___x_1249_);
v___x_1251_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1250_, v___y_1240_);
lean_dec_ref(v___x_1250_);
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___y_1240_;
v___y_1219_ = v___y_1244_;
v___y_1220_ = v___y_1241_;
v___y_1221_ = v___y_1242_;
v___y_1222_ = v___y_1243_;
v___y_1223_ = v___x_1251_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1252_; 
lean_inc(v___y_1240_);
v___x_1252_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1240_);
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___y_1240_;
v___y_1219_ = v___y_1244_;
v___y_1220_ = v___y_1241_;
v___y_1221_ = v___y_1242_;
v___y_1222_ = v___y_1243_;
v___y_1223_ = v___x_1252_;
goto v___jp_1216_;
}
}
v___jp_1253_:
{
if (v_a_1261_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = l_IO_FS_createDirAll(v___y_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref_known(v___x_1262_, 1);
v___x_1263_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1264_ = l_IO_FS_writeFile(v___y_1255_, v___x_1263_);
lean_dec_ref(v___y_1255_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref_known(v___x_1264_, 1);
v___y_1239_ = v___y_1254_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v_a_931_;
goto v___jp_1238_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1269_ = lean_io_error_to_string(v_a_1265_);
v___x_1270_ = 3;
v___x_1271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*1, v___x_1270_);
lean_inc_ref(v_a_931_);
v___x_1272_ = lean_apply_2(v_a_931_, v___x_1271_, lean_box(0));
v___x_1273_ = lean_box(0);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1273_);
v___x_1275_ = v___x_1267_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1278_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1280_ = v___x_1262_;
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1262_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1282_ = lean_io_error_to_string(v_a_1278_);
v___x_1283_ = 3;
v___x_1284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
lean_inc_ref(v_a_931_);
v___x_1285_ = lean_apply_2(v_a_931_, v___x_1284_, lean_box(0));
v___x_1286_ = lean_box(0);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1286_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1255_);
v___y_1239_ = v___y_1254_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v_a_931_;
goto v___jp_1238_;
}
}
v___jp_1294_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v___y_1299_);
lean_inc(v___y_1296_);
lean_inc(v_name_926_);
v___x_1300_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_927_, v_lang_928_, v_name_926_, v___y_1296_, v___y_1299_);
v___x_1301_ = l_IO_FS_writeFile(v_configFile_1293_, v___x_1300_);
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_configFile_1293_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_dec_ref_known(v___x_1301_, 1);
if (lean_obj_tag(v___y_1297_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; uint8_t v___x_1309_; 
v_val_1302_ = lean_ctor_get(v___y_1297_, 0);
lean_inc_n(v_val_1302_, 2);
lean_dec_ref_known(v___y_1297_, 1);
v___x_1303_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1304_ = l_System_FilePath_withExtension(v_val_1302_, v___x_1303_);
v___x_1305_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1304_);
v___x_1306_ = l_Lake_joinRelative(v___x_1304_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1308_ = l_System_FilePath_pathExists(v___x_1306_);
v___x_1309_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1309_ == 0)
{
v___y_1254_ = v___y_1295_;
v___y_1255_ = v___x_1306_;
v___y_1256_ = v___y_1296_;
v___y_1257_ = v_val_1302_;
v___y_1258_ = v___y_1298_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___x_1304_;
v_a_1261_ = v___x_1308_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1307_, v___x_1311_, v___x_1312_, v___x_1310_, v_a_931_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref_known(v___x_1313_, 1);
v___y_1254_ = v___y_1295_;
v___y_1255_ = v___x_1306_;
v___y_1256_ = v___y_1296_;
v___y_1257_ = v_val_1302_;
v___y_1258_ = v___y_1298_;
v___y_1259_ = v___y_1299_;
v___y_1260_ = v___x_1304_;
v_a_1261_ = v___x_1308_;
goto v___jp_1253_;
}
else
{
lean_dec_ref(v___x_1306_);
lean_dec_ref(v___x_1304_);
lean_dec(v_val_1302_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1313_;
}
}
}
else
{
lean_dec(v___y_1297_);
v___y_1211_ = v___y_1295_;
v___y_1212_ = v___y_1296_;
v___y_1213_ = v___y_1298_;
v___y_1214_ = v___y_1299_;
v___y_1215_ = v_a_931_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1314_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1316_ = v___x_1301_;
v_isShared_1317_ = v_isSharedCheck_1326_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1301_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1326_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1318_ = lean_io_error_to_string(v_a_1314_);
v___x_1319_ = 3;
v___x_1320_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*1, v___x_1319_);
lean_inc_ref(v_a_931_);
v___x_1321_ = lean_apply_2(v_a_931_, v___x_1320_, lean_box(0));
v___x_1322_ = lean_box(0);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1322_);
v___x_1324_ = v___x_1316_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
v___jp_1327_:
{
lean_object* v_lean_1330_; lean_object* v_toolchain_1331_; lean_object* v___x_1332_; 
v_lean_1330_ = lean_ctor_get(v_env_929_, 1);
v_toolchain_1331_ = lean_ctor_get(v_env_929_, 19);
lean_inc_ref(v_toolchain_1331_);
v___x_1332_ = l_Lake_ToolchainVer_ofString(v_toolchain_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_ver_1333_; lean_object* v___x_1334_; 
v_ver_1333_ = lean_ctor_get(v___x_1332_, 1);
lean_inc_ref(v_ver_1333_);
lean_dec_ref_known(v___x_1332_, 2);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_ver_1333_);
lean_inc_ref(v_lean_1330_);
lean_inc_ref(v_toolchain_1331_);
v___y_1295_ = v_toolchain_1331_;
v___y_1296_ = v_fst_1328_;
v___y_1297_ = v_snd_1329_;
v___y_1298_ = v_lean_1330_;
v___y_1299_ = v___x_1334_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1332_);
v___x_1335_ = lean_box(0);
lean_inc_ref(v_lean_1330_);
lean_inc_ref(v_toolchain_1331_);
v___y_1295_ = v_toolchain_1331_;
v___y_1296_ = v_fst_1328_;
v___y_1297_ = v_snd_1329_;
v___y_1298_ = v_lean_1330_;
v___y_1299_ = v___x_1335_;
goto v___jp_1294_;
}
}
v___jp_1336_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(0);
lean_inc(v_name_926_);
v_fst_1328_ = v_name_926_;
v_snd_1329_ = v___x_1337_;
goto v___jp_1327_;
}
v___jp_1338_:
{
if (v_a_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___y_1339_);
v_fst_1328_ = v___y_1340_;
v_snd_1329_ = v___x_1342_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1343_; 
lean_dec_ref(v___y_1339_);
v___x_1343_ = lean_box(0);
v_fst_1328_ = v___y_1340_;
v_snd_1329_ = v___x_1343_;
goto v___jp_1327_;
}
}
v___jp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1347_ = lean_box(v_tmp_927_);
v___x_1348_ = lean_obj_tag_nat(v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
if (v_a_1346_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; 
lean_inc(v_name_926_);
v___x_1351_ = l_Lake_toUpperCamelCase(v_name_926_);
lean_inc(v___x_1351_);
v___x_1352_ = l_Lean_modToFilePath(v_dir_925_, v___x_1351_, v___y_1345_);
v___x_1353_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1354_ = l_System_FilePath_pathExists(v___x_1352_);
v___x_1355_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1355_ == 0)
{
v___y_1339_ = v___x_1352_;
v___y_1340_ = v___x_1351_;
v_a_1341_ = v___x_1354_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1353_, v___x_1357_, v___x_1358_, v___x_1356_, v_a_931_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
v___y_1339_ = v___x_1352_;
v___y_1340_ = v___x_1351_;
v_a_1341_ = v___x_1354_;
goto v___jp_1338_;
}
else
{
lean_dec_ref(v___x_1352_);
lean_dec(v___x_1351_);
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1359_;
}
}
}
else
{
goto v___jp_1336_;
}
}
else
{
goto v___jp_1336_;
}
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1361_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_926_);
v___x_1362_ = l_Lean_modToFilePath(v_dir_925_, v_name_926_, v___x_1361_);
v___x_1363_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1364_ = l_System_FilePath_pathExists(v___x_1362_);
lean_dec_ref(v___x_1362_);
v___x_1365_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1365_ == 0)
{
v___y_1345_ = v___x_1361_;
v_a_1346_ = v___x_1364_;
goto v___jp_1344_;
}
else
{
lean_object* v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_box(0);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1363_, v___x_1367_, v___x_1368_, v___x_1366_, v_a_931_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref_known(v___x_1369_, 1);
v___y_1345_ = v___x_1361_;
v_a_1346_ = v___x_1364_;
goto v___jp_1344_;
}
else
{
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1369_;
}
}
}
v___jp_1370_:
{
if (v_a_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_925_);
v___x_1374_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_925_, v_tmp_927_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 2);
v___x_1376_ = lean_array_get_size(v_a_1375_);
v___x_1377_ = lean_nat_dec_lt(v___x_1372_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_a_1375_);
goto v___jp_1360_;
}
else
{
lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = lean_usize_of_nat(v___x_1376_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1375_, v___x_1379_, v___x_1380_, v___x_1378_, v_a_931_);
lean_dec(v_a_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec_ref_known(v___x_1381_, 1);
goto v___jp_1360_;
}
else
{
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
return v___x_1381_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v_a_1382_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1374_, 2);
v___x_1383_ = lean_array_get_size(v_a_1382_);
v___x_1384_ = lean_nat_dec_lt(v___x_1372_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v_a_1382_);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = lean_usize_of_nat(v___x_1383_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1382_, v___x_1388_, v___x_1389_, v___x_1387_, v_a_931_);
lean_dec(v_a_1382_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1398_);
v___x_1392_ = v___x_1390_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___x_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1387_);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1387_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_configFile_1293_);
lean_dec_ref(v_env_929_);
lean_dec(v_name_926_);
lean_dec_ref(v_dir_925_);
v___x_1399_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_931_);
v___x_1400_ = lean_apply_2(v_a_931_, v___x_1399_, lean_box(0));
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1410_, lean_object* v_name_1411_, lean_object* v_tmp_1412_, lean_object* v_lang_1413_, lean_object* v_env_1414_, lean_object* v_offline_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
uint8_t v_tmp_boxed_1418_; uint8_t v_lang_boxed_1419_; uint8_t v_offline_boxed_1420_; lean_object* v_res_1421_; 
v_tmp_boxed_1418_ = lean_unbox(v_tmp_1412_);
v_lang_boxed_1419_ = lean_unbox(v_lang_1413_);
v_offline_boxed_1420_ = lean_unbox(v_offline_1415_);
v_res_1421_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1410_, v_name_1411_, v_tmp_boxed_1418_, v_lang_boxed_1419_, v_env_1414_, v_offline_boxed_1420_, v_a_1416_);
lean_dec_ref(v_a_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(lean_object* v_a_1422_, lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = 0;
return v___x_1424_;
}
else
{
lean_object* v_head_1425_; lean_object* v_tail_1426_; uint8_t v___x_1427_; 
v_head_1425_ = lean_ctor_get(v_x_1423_, 0);
v_tail_1426_ = lean_ctor_get(v_x_1423_, 1);
v___x_1427_ = lean_string_dec_eq(v_a_1422_, v_head_1425_);
if (v___x_1427_ == 0)
{
v_x_1423_ = v_tail_1426_;
goto _start;
}
else
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3___boxed(lean_object* v_a_1429_, lean_object* v_x_1430_){
_start:
{
uint8_t v_res_1431_; lean_object* v_r_1432_; 
v_res_1431_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v_a_1429_, v_x_1430_);
lean_dec(v_x_1430_);
lean_dec_ref(v_a_1429_);
v_r_1432_ = lean_box(v_res_1431_);
return v_r_1432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1433_, lean_object* v_pos_1434_){
_start:
{
lean_object* v_str_1435_; lean_object* v_startInclusive_1436_; lean_object* v_endExclusive_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v_decide_1441_; 
v_str_1435_ = lean_ctor_get(v_s_1433_, 0);
v_startInclusive_1436_ = lean_ctor_get(v_s_1433_, 1);
v_endExclusive_1437_ = lean_ctor_get(v_s_1433_, 2);
v___x_1438_ = lean_nat_add(v_startInclusive_1436_, v_pos_1434_);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_nat_sub(v_endExclusive_1437_, v___x_1438_);
v_decide_1441_ = lean_nat_dec_eq(v___x_1439_, v___x_1440_);
lean_dec(v___x_1440_);
if (v_decide_1441_ == 0)
{
uint32_t v___x_1442_; uint32_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_string_utf8_get_fast(v_str_1435_, v___x_1438_);
v___x_1443_ = 46;
v___x_1444_ = lean_uint32_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_dec(v___x_1438_);
return v_pos_1434_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1445_ = lean_string_utf8_next_fast(v_str_1435_, v___x_1438_);
v___x_1446_ = lean_nat_sub(v___x_1445_, v___x_1438_);
lean_dec(v___x_1438_);
v___x_1447_ = lean_nat_add(v_pos_1434_, v___x_1446_);
lean_dec(v___x_1446_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_pos_1434_, v___x_1448_);
v___x_1450_ = lean_nat_dec_le(v___x_1449_, v___x_1447_);
lean_dec(v___x_1449_);
if (v___x_1450_ == 0)
{
lean_dec(v___x_1447_);
return v_pos_1434_;
}
else
{
lean_dec(v_pos_1434_);
v_pos_1434_ = v___x_1447_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1438_);
return v_pos_1434_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1452_, lean_object* v_pos_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1452_, v_pos_1453_);
lean_dec_ref(v_s_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(uint32_t v_a_1455_, lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 0)
{
uint8_t v___x_1457_; 
v___x_1457_ = 0;
return v___x_1457_;
}
else
{
lean_object* v_head_1458_; lean_object* v_tail_1459_; uint32_t v___x_1460_; uint8_t v___x_1461_; 
v_head_1458_ = lean_ctor_get(v_x_1456_, 0);
v_tail_1459_ = lean_ctor_get(v_x_1456_, 1);
v___x_1460_ = lean_unbox_uint32(v_head_1458_);
v___x_1461_ = lean_uint32_dec_eq(v_a_1455_, v___x_1460_);
if (v___x_1461_ == 0)
{
v_x_1456_ = v_tail_1459_;
goto _start;
}
else
{
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_a_1463_, lean_object* v_x_1464_){
_start:
{
uint32_t v_a_boxed_1465_; uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_a_boxed_1465_ = lean_unbox_uint32(v_a_1463_);
lean_dec(v_a_1463_);
v_res_1466_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_a_boxed_1465_, v_x_1464_);
lean_dec(v_x_1464_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = 92;
v___x_1469_ = lean_box_uint32(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1;
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1470_);
return v___x_1472_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = 47;
v___x_1474_ = lean_box_uint32(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0);
v___x_1476_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1;
v___x_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(lean_object* v_s_1478_, lean_object* v_a_1479_, uint8_t v_b_1480_){
_start:
{
lean_object* v_str_1481_; lean_object* v_startInclusive_1482_; lean_object* v_endExclusive_1483_; lean_object* v___x_1484_; uint8_t v_decide_1485_; 
v_str_1481_ = lean_ctor_get(v_s_1478_, 0);
v_startInclusive_1482_ = lean_ctor_get(v_s_1478_, 1);
v_endExclusive_1483_ = lean_ctor_get(v_s_1478_, 2);
v___x_1484_ = lean_nat_sub(v_endExclusive_1483_, v_startInclusive_1482_);
v_decide_1485_ = lean_nat_dec_eq(v_a_1479_, v___x_1484_);
lean_dec(v___x_1484_);
if (v_decide_1485_ == 0)
{
lean_object* v___x_1486_; uint32_t v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1486_ = lean_nat_add(v_startInclusive_1482_, v_a_1479_);
lean_dec(v_a_1479_);
v___x_1487_ = lean_string_utf8_get_fast(v_str_1481_, v___x_1486_);
v___x_1488_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1);
v___x_1489_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_string_utf8_next_fast(v_str_1481_, v___x_1486_);
lean_dec(v___x_1486_);
v___x_1491_ = lean_nat_sub(v___x_1490_, v_startInclusive_1482_);
v_a_1479_ = v___x_1491_;
v_b_1480_ = v___x_1489_;
goto _start;
}
else
{
lean_dec(v___x_1486_);
return v___x_1489_;
}
}
else
{
lean_dec(v_a_1479_);
return v_b_1480_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___boxed(lean_object* v_s_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_){
_start:
{
uint8_t v_b_boxed_1496_; uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_b_boxed_1496_ = lean_unbox(v_b_1495_);
v_res_1497_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1493_, v_a_1494_, v_b_boxed_1496_);
lean_dec_ref(v_s_1493_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object* v_s_1499_){
_start:
{
lean_object* v_searcher_1500_; uint8_t v___x_1501_; uint8_t v___x_1502_; 
v_searcher_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = 0;
v___x_1502_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1499_, v_searcher_1500_, v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object* v_s_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v_s_1503_);
lean_dec_ref(v_s_1503_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_string_utf8_byte_size(v_pkgName_1526_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_nat_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v_decide_1544_; 
lean_inc_ref(v_pkgName_1526_);
v___x_1542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1542_, 0, v_pkgName_1526_);
lean_ctor_set(v___x_1542_, 1, v___x_1540_);
lean_ctor_set(v___x_1542_, 2, v___x_1539_);
v___x_1543_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1542_, v___x_1540_);
v_decide_1544_ = lean_nat_dec_eq(v___x_1543_, v___x_1539_);
lean_dec(v___x_1543_);
if (v_decide_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v___x_1542_);
lean_dec_ref_known(v___x_1542_, 3);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1526_, v___x_1540_);
v___x_1547_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7));
v___x_1548_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1546_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_a_1527_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1551_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9));
v___x_1552_ = lean_array_get_size(v_a_1527_);
v___x_1553_ = lean_array_push(v_a_1527_, v___x_1551_);
v___x_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
return v___x_1554_;
}
}
else
{
goto v___jp_1529_;
}
}
else
{
lean_dec_ref_known(v___x_1542_, 3);
goto v___jp_1529_;
}
}
else
{
goto v___jp_1529_;
}
v___jp_1529_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1530_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1531_ = lean_string_append(v___x_1530_, v_pkgName_1526_);
lean_dec_ref(v_pkgName_1526_);
v___x_1532_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1533_ = lean_string_append(v___x_1531_, v___x_1532_);
v___x_1534_ = 3;
v___x_1535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*1, v___x_1534_);
v___x_1536_ = lean_array_get_size(v_a_1527_);
v___x_1537_ = lean_array_push(v_a_1527_, v___x_1535_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1555_, v_a_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object* v_s_1559_, lean_object* v_inst_1560_, lean_object* v_R_1561_, lean_object* v_a_1562_, uint8_t v_b_1563_, lean_object* v_c_1564_){
_start:
{
uint8_t v___x_1565_; 
v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1559_, v_a_1562_, v_b_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object* v_s_1566_, lean_object* v_inst_1567_, lean_object* v_R_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v_c_1571_){
_start:
{
uint8_t v_b_boxed_1572_; uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_b_boxed_1572_ = lean_unbox(v_b_1570_);
v_res_1573_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(v_s_1566_, v_inst_1567_, v_R_1568_, v_a_1569_, v_b_boxed_1572_, v_c_1571_);
lean_dec_ref(v_s_1566_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1575_, lean_object* v_dir_1576_, lean_object* v_name_1577_, uint8_t v_tmp_1578_, uint8_t v_lang_1579_, lean_object* v_env_1580_, uint8_t v_offline_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v___y_1585_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v_a_1615_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; uint8_t v_a_1723_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; uint8_t v_a_1780_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; uint8_t v_a_1810_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v_a_1911_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v_configFile_1943_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v_a_1991_; lean_object* v___y_1995_; uint8_t v_a_1996_; uint8_t v_a_2021_; lean_object* v___x_2053_; uint8_t v___x_2054_; uint8_t v___x_2055_; 
v___x_1583_ = l_Lake_defaultConfigFile;
v___x_1941_ = l_Lake_ConfigLang_fileExtension(v_lang_1579_);
v___x_1942_ = l_System_FilePath_addExtension(v___x_1583_, v___x_1941_);
lean_dec_ref(v___x_1941_);
lean_inc_ref(v_dir_1576_);
v_configFile_1943_ = l_Lake_joinRelative(v_dir_1576_, v___x_1942_);
v___x_2053_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2054_ = l_System_FilePath_pathExists(v_configFile_1943_);
v___x_2055_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2055_ == 0)
{
v_a_2021_ = v___x_2054_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2053_, v___x_2057_, v___x_2058_, v___x_2056_, v_a_1575_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_dec_ref_known(v___x_2059_, 1);
v_a_2021_ = v___x_2054_;
goto v___jp_2020_;
}
else
{
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_2059_;
}
}
v___jp_1584_:
{
if (v_offline_1581_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_box(0);
v___x_1589_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1576_);
v___x_1590_ = l_Lake_joinRelative(v_dir_1576_, v___x_1589_);
lean_inc_ref(v___x_1590_);
v___x_1591_ = l_Lake_joinRelative(v___x_1590_, v___x_1583_);
v___x_1592_ = l_Lake_defaultManifestFile;
v___x_1593_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1594_ = lean_box(1);
v___x_1595_ = l_Lean_Options_empty;
v___x_1596_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1597_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_1597_, 0, v_env_1580_);
lean_ctor_set(v___x_1597_, 1, v___x_1586_);
lean_ctor_set(v___x_1597_, 2, v_dir_1576_);
lean_ctor_set(v___x_1597_, 3, v___x_1587_);
lean_ctor_set(v___x_1597_, 4, v___x_1588_);
lean_ctor_set(v___x_1597_, 5, v___x_1589_);
lean_ctor_set(v___x_1597_, 6, v___x_1590_);
lean_ctor_set(v___x_1597_, 7, v___x_1583_);
lean_ctor_set(v___x_1597_, 8, v___x_1591_);
lean_ctor_set(v___x_1597_, 9, v___x_1586_);
lean_ctor_set(v___x_1597_, 10, v___x_1592_);
lean_ctor_set(v___x_1597_, 11, v___x_1593_);
lean_ctor_set(v___x_1597_, 12, v___x_1594_);
lean_ctor_set(v___x_1597_, 13, v___x_1595_);
lean_ctor_set(v___x_1597_, 14, v___x_1596_);
lean_ctor_set(v___x_1597_, 15, v___x_1596_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*16, v_offline_1581_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*16 + 1, v_offline_1581_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*16 + 2, v_offline_1581_);
v___x_1598_ = l_Lean_NameSet_empty;
v___x_1599_ = l_Lake_updateManifest(v___x_1597_, v___x_1598_, v___y_1585_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
v___jp_1602_:
{
if (lean_obj_tag(v___y_1603_) == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1604_);
v___x_1606_ = lean_apply_2(v___y_1604_, v___x_1605_, lean_box(0));
v___y_1585_ = v___y_1604_;
goto v___jp_1584_;
}
else
{
lean_dec_ref_known(v___y_1603_, 1);
v___y_1585_ = v___y_1604_;
goto v___jp_1584_;
}
}
v___jp_1607_:
{
switch(v_tmp_1578_)
{
case 3:
{
v___y_1603_ = v___y_1608_;
v___y_1604_ = v___y_1609_;
goto v___jp_1602_;
}
case 4:
{
v___y_1603_ = v___y_1608_;
v___y_1604_ = v___y_1609_;
goto v___jp_1602_;
}
default: 
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v___y_1608_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
}
v___jp_1612_:
{
if (v_a_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1614_);
v___x_1617_ = lean_apply_2(v___y_1614_, v___x_1616_, lean_box(0));
v___y_1608_ = v___y_1613_;
v___y_1609_ = v___y_1614_;
goto v___jp_1607_;
}
else
{
v___y_1608_ = v___y_1613_;
v___y_1609_ = v___y_1614_;
goto v___jp_1607_;
}
}
v___jp_1618_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1623_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1576_);
v___x_1624_ = l_Lake_joinRelative(v_dir_1576_, v___x_1623_);
v___x_1625_ = 4;
v___x_1626_ = lean_io_prim_handle_mk(v___x_1624_, v___x_1625_);
lean_dec_ref(v___x_1624_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1629_ = lean_io_prim_handle_put_str(v_a_1627_, v___x_1628_);
lean_dec(v_a_1627_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
lean_dec_ref_known(v___x_1629_, 1);
v___x_1630_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1576_);
v___x_1631_ = l_Lake_joinRelative(v_dir_1576_, v___x_1630_);
v___x_1632_ = lean_string_utf8_byte_size(v___y_1621_);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = lean_nat_dec_eq(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v___y_1619_);
v___x_1635_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1636_ = lean_string_append(v___y_1621_, v___x_1635_);
v___x_1637_ = l_IO_FS_writeFile(v___x_1631_, v___x_1636_);
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1631_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_dec_ref_known(v___x_1637_, 1);
v___y_1608_ = v___y_1620_;
v___y_1609_ = v___y_1622_;
goto v___jp_1607_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v___y_1620_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1642_ = lean_io_error_to_string(v_a_1638_);
v___x_1643_ = 3;
v___x_1644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*1, v___x_1643_);
lean_inc_ref(v___y_1622_);
v___x_1645_ = lean_apply_2(v___y_1622_, v___x_1644_, lean_box(0));
v___x_1646_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1646_);
v___x_1648_ = v___x_1640_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_githash_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
lean_dec_ref(v___y_1621_);
v_githash_1651_ = lean_ctor_get(v___y_1619_, 1);
lean_inc_ref(v_githash_1651_);
lean_dec_ref(v___y_1619_);
v___x_1652_ = lean_string_utf8_byte_size(v_githash_1651_);
lean_dec_ref(v_githash_1651_);
v___x_1653_ = lean_nat_dec_eq(v___x_1652_, v___x_1633_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1655_ = l_System_FilePath_pathExists(v___x_1631_);
lean_dec_ref(v___x_1631_);
v___x_1656_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1656_ == 0)
{
v___y_1613_ = v___y_1620_;
v___y_1614_ = v___y_1622_;
v_a_1615_ = v___x_1655_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1654_, v___x_1658_, v___x_1659_, v___x_1657_, v___y_1622_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec_ref_known(v___x_1660_, 1);
v___y_1613_ = v___y_1620_;
v___y_1614_ = v___y_1622_;
v_a_1615_ = v___x_1655_;
goto v___jp_1612_;
}
else
{
lean_dec(v___y_1620_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
return v___x_1660_;
}
}
}
else
{
lean_dec_ref(v___x_1631_);
v___y_1608_ = v___y_1620_;
v___y_1609_ = v___y_1622_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v_a_1661_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1663_ = v___x_1629_;
v_isShared_1664_ = v_isSharedCheck_1673_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1629_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1673_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1665_ = lean_io_error_to_string(v_a_1661_);
v___x_1666_ = 3;
v___x_1667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*1, v___x_1666_);
lean_inc_ref(v___y_1622_);
v___x_1668_ = lean_apply_2(v___y_1622_, v___x_1667_, lean_box(0));
v___x_1669_ = lean_box(0);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1669_);
v___x_1671_ = v___x_1663_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v_a_1674_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1676_ = v___x_1626_;
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1626_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1686_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1678_ = lean_io_error_to_string(v_a_1674_);
v___x_1679_ = 3;
v___x_1680_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*1, v___x_1679_);
lean_inc_ref(v___y_1622_);
v___x_1681_ = lean_apply_2(v___y_1622_, v___x_1680_, lean_box(0));
v___x_1682_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1682_);
v___x_1684_ = v___x_1676_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
v___jp_1687_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1691_);
v___x_1693_ = lean_apply_2(v___y_1691_, v___x_1692_, lean_box(0));
v___y_1619_ = v___y_1688_;
v___y_1620_ = v___y_1689_;
v___y_1621_ = v___y_1690_;
v___y_1622_ = v___y_1691_;
goto v___jp_1618_;
}
v___jp_1694_:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = l_Lake_Git_upstreamBranch;
v___x_1700_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1576_);
v___x_1703_ = l_Lake_GitRepo_checkoutBranch(v___x_1699_, v_dir_1576_, v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 1);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 2);
v___x_1705_ = lean_array_get_size(v_a_1704_);
v___x_1706_ = lean_nat_dec_lt(v___x_1701_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v_a_1704_);
v___y_1619_ = v___y_1695_;
v___y_1620_ = v___y_1696_;
v___y_1621_ = v___y_1697_;
v___y_1622_ = v___y_1698_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = ((size_t)0ULL);
v___x_1709_ = lean_usize_of_nat(v___x_1705_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1704_, v___x_1708_, v___x_1709_, v___x_1707_, v___y_1698_);
lean_dec(v_a_1704_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_dec_ref_known(v___x_1710_, 1);
v___y_1619_ = v___y_1695_;
v___y_1620_ = v___y_1696_;
v___y_1621_ = v___y_1697_;
v___y_1622_ = v___y_1698_;
goto v___jp_1618_;
}
else
{
lean_dec_ref_known(v___x_1710_, 1);
v___y_1688_ = v___y_1695_;
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___y_1697_;
v___y_1691_ = v___y_1698_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_a_1711_ = lean_ctor_get(v___x_1703_, 1);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1703_, 2);
v___x_1712_ = lean_array_get_size(v_a_1711_);
v___x_1713_ = lean_nat_dec_lt(v___x_1701_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec(v_a_1711_);
v___y_1688_ = v___y_1695_;
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___y_1697_;
v___y_1691_ = v___y_1698_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = lean_usize_of_nat(v___x_1712_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1711_, v___x_1715_, v___x_1716_, v___x_1714_, v___y_1698_);
lean_dec(v_a_1711_);
lean_dec_ref(v___x_1717_);
v___y_1688_ = v___y_1695_;
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___y_1697_;
v___y_1691_ = v___y_1698_;
goto v___jp_1687_;
}
}
}
else
{
v___y_1619_ = v___y_1695_;
v___y_1620_ = v___y_1696_;
v___y_1621_ = v___y_1697_;
v___y_1622_ = v___y_1698_;
goto v___jp_1618_;
}
}
v___jp_1718_:
{
if (v_a_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1576_);
v___x_1726_ = l_Lake_GitRepo_quietInit(v_dir_1576_, v___x_1725_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 2);
v___x_1728_ = lean_array_get_size(v_a_1727_);
v___x_1729_ = lean_nat_dec_lt(v___x_1724_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec(v_a_1727_);
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___y_1720_;
v___y_1697_ = v___y_1721_;
v___y_1698_ = v___y_1722_;
goto v___jp_1694_;
}
else
{
lean_object* v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = ((size_t)0ULL);
v___x_1732_ = lean_usize_of_nat(v___x_1728_);
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1727_, v___x_1731_, v___x_1732_, v___x_1730_, v___y_1722_);
lean_dec(v_a_1727_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref_known(v___x_1733_, 1);
v___y_1695_ = v___y_1719_;
v___y_1696_ = v___y_1720_;
v___y_1697_ = v___y_1721_;
v___y_1698_ = v___y_1722_;
goto v___jp_1694_;
}
else
{
lean_dec_ref_known(v___x_1733_, 1);
v___y_1688_ = v___y_1719_;
v___y_1689_ = v___y_1720_;
v___y_1690_ = v___y_1721_;
v___y_1691_ = v___y_1722_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v_a_1734_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1726_, 2);
v___x_1735_ = lean_array_get_size(v_a_1734_);
v___x_1736_ = lean_nat_dec_lt(v___x_1724_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_dec(v_a_1734_);
v___y_1688_ = v___y_1719_;
v___y_1689_ = v___y_1720_;
v___y_1690_ = v___y_1721_;
v___y_1691_ = v___y_1722_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = lean_usize_of_nat(v___x_1735_);
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1734_, v___x_1738_, v___x_1739_, v___x_1737_, v___y_1722_);
lean_dec(v_a_1734_);
lean_dec_ref(v___x_1740_);
v___y_1688_ = v___y_1719_;
v___y_1689_ = v___y_1720_;
v___y_1690_ = v___y_1721_;
v___y_1691_ = v___y_1722_;
goto v___jp_1687_;
}
}
}
else
{
v___y_1619_ = v___y_1719_;
v___y_1620_ = v___y_1720_;
v___y_1621_ = v___y_1721_;
v___y_1622_ = v___y_1722_;
goto v___jp_1618_;
}
}
v___jp_1741_:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; 
v___x_1746_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1576_);
v___x_1747_ = l_Lake_GitRepo_insideWorkTree(v_dir_1576_);
v___x_1748_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1748_ == 0)
{
v___y_1719_ = v___y_1742_;
v___y_1720_ = v___y_1743_;
v___y_1721_ = v___y_1744_;
v___y_1722_ = v___y_1745_;
v_a_1723_ = v___x_1747_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1746_, v___x_1750_, v___x_1751_, v___x_1749_, v___y_1745_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec_ref_known(v___x_1752_, 1);
v___y_1719_ = v___y_1742_;
v___y_1720_ = v___y_1743_;
v___y_1721_ = v___y_1744_;
v___y_1722_ = v___y_1745_;
v_a_1723_ = v___x_1747_;
goto v___jp_1718_;
}
else
{
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
return v___x_1752_;
}
}
}
v___jp_1753_:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_IO_FS_writeFile(v___y_1756_, v___y_1759_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1756_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec_ref_known(v___x_1760_, 1);
v___y_1742_ = v___y_1754_;
v___y_1743_ = v___y_1755_;
v___y_1744_ = v___y_1757_;
v___y_1745_ = v___y_1758_;
goto v___jp_1741_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v_env_1580_);
lean_dec_ref(v_dir_1576_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1765_ = lean_io_error_to_string(v_a_1761_);
v___x_1766_ = 3;
v___x_1767_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*1, v___x_1766_);
lean_inc_ref(v___y_1758_);
v___x_1768_ = lean_apply_2(v___y_1758_, v___x_1767_, lean_box(0));
v___x_1769_ = lean_box(0);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1769_);
v___x_1771_ = v___x_1763_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
v___jp_1774_:
{
if (v_a_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1781_ = lean_box(v_tmp_1578_);
v___x_1782_ = lean_obj_tag_nat(v___x_1781_);
lean_dec(v___x_1781_);
v___x_1783_ = lean_unsigned_to_nat(4u);
v___x_1784_ = lean_nat_dec_eq(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1577_);
v___x_1786_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1785_);
lean_dec_ref(v___x_1785_);
v___y_1754_ = v___y_1775_;
v___y_1755_ = v___y_1776_;
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1779_;
v___y_1758_ = v___y_1778_;
v___y_1759_ = v___x_1786_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1577_);
v___x_1788_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1787_);
lean_dec_ref(v___x_1787_);
v___y_1754_ = v___y_1775_;
v___y_1755_ = v___y_1776_;
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1779_;
v___y_1758_ = v___y_1778_;
v___y_1759_ = v___x_1788_;
goto v___jp_1753_;
}
}
else
{
lean_dec_ref(v___y_1777_);
lean_dec(v_name_1577_);
v___y_1742_ = v___y_1775_;
v___y_1743_ = v___y_1776_;
v___y_1744_ = v___y_1779_;
v___y_1745_ = v___y_1778_;
goto v___jp_1741_;
}
}
v___jp_1789_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1794_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_1576_);
v___x_1795_ = l_Lake_joinRelative(v_dir_1576_, v___x_1794_);
v___x_1796_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1797_ = l_System_FilePath_pathExists(v___x_1795_);
v___x_1798_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1798_ == 0)
{
v___y_1775_ = v___y_1790_;
v___y_1776_ = v___y_1791_;
v___y_1777_ = v___x_1795_;
v___y_1778_ = v___y_1793_;
v___y_1779_ = v___y_1792_;
v_a_1780_ = v___x_1797_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1796_, v___x_1800_, v___x_1801_, v___x_1799_, v___y_1793_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref_known(v___x_1802_, 1);
v___y_1775_ = v___y_1790_;
v___y_1776_ = v___y_1791_;
v___y_1777_ = v___x_1795_;
v___y_1778_ = v___y_1793_;
v___y_1779_ = v___y_1792_;
v_a_1780_ = v___x_1797_;
goto v___jp_1774_;
}
else
{
lean_dec_ref(v___x_1795_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_1802_;
}
}
}
v___jp_1803_:
{
if (v_a_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1811_ = lean_box(v_tmp_1578_);
v___x_1812_ = lean_obj_tag_nat(v___x_1811_);
lean_dec(v___x_1811_);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_dec_eq(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1805_);
v___x_1816_ = l_IO_FS_writeFile(v___y_1806_, v___x_1815_);
lean_dec_ref(v___x_1815_);
lean_dec_ref(v___y_1806_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_dec_ref_known(v___x_1816_, 1);
v___y_1790_ = v___y_1804_;
v___y_1791_ = v___y_1807_;
v___y_1792_ = v___y_1808_;
v___y_1793_ = v___y_1809_;
goto v___jp_1789_;
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1804_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1821_ = lean_io_error_to_string(v_a_1817_);
v___x_1822_ = 3;
v___x_1823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*1, v___x_1822_);
lean_inc_ref(v___y_1809_);
v___x_1824_ = lean_apply_2(v___y_1809_, v___x_1823_, lean_box(0));
v___x_1825_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1825_);
v___x_1827_ = v___x_1819_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v___y_1805_);
v___x_1830_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1831_ = l_IO_FS_writeFile(v___y_1806_, v___x_1830_);
lean_dec_ref(v___y_1806_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref_known(v___x_1831_, 1);
v___y_1790_ = v___y_1804_;
v___y_1791_ = v___y_1807_;
v___y_1792_ = v___y_1808_;
v___y_1793_ = v___y_1809_;
goto v___jp_1789_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1804_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1836_ = lean_io_error_to_string(v_a_1832_);
v___x_1837_ = 3;
v___x_1838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*1, v___x_1837_);
lean_inc_ref(v___y_1809_);
v___x_1839_ = lean_apply_2(v___y_1809_, v___x_1838_, lean_box(0));
v___x_1840_ = lean_box(0);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1840_);
v___x_1842_ = v___x_1834_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
v___y_1790_ = v___y_1804_;
v___y_1791_ = v___y_1807_;
v___y_1792_ = v___y_1808_;
v___y_1793_ = v___y_1809_;
goto v___jp_1789_;
}
}
v___jp_1845_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; 
v___x_1851_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1576_);
v___x_1852_ = l_Lake_joinRelative(v_dir_1576_, v___x_1851_);
v___x_1853_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1854_ = l_System_FilePath_pathExists(v___x_1852_);
v___x_1855_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1855_ == 0)
{
v___y_1804_ = v___y_1847_;
v___y_1805_ = v___y_1846_;
v___y_1806_ = v___x_1852_;
v___y_1807_ = v___y_1848_;
v___y_1808_ = v___y_1849_;
v___y_1809_ = v___y_1850_;
v_a_1810_ = v___x_1854_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1853_, v___x_1857_, v___x_1858_, v___x_1856_, v___y_1850_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_dec_ref_known(v___x_1859_, 1);
v___y_1804_ = v___y_1847_;
v___y_1805_ = v___y_1846_;
v___y_1806_ = v___x_1852_;
v___y_1807_ = v___y_1848_;
v___y_1808_ = v___y_1849_;
v___y_1809_ = v___y_1850_;
v_a_1810_ = v___x_1854_;
goto v___jp_1803_;
}
else
{
lean_dec_ref(v___x_1852_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_1859_;
}
}
}
v___jp_1860_:
{
switch(v_tmp_1578_)
{
case 0:
{
v___y_1846_ = v___y_1862_;
v___y_1847_ = v___y_1861_;
v___y_1848_ = v___y_1863_;
v___y_1849_ = v___y_1864_;
v___y_1850_ = v___y_1865_;
goto v___jp_1845_;
}
case 1:
{
v___y_1846_ = v___y_1862_;
v___y_1847_ = v___y_1861_;
v___y_1848_ = v___y_1863_;
v___y_1849_ = v___y_1864_;
v___y_1850_ = v___y_1865_;
goto v___jp_1845_;
}
default: 
{
lean_dec(v___y_1862_);
v___y_1790_ = v___y_1861_;
v___y_1791_ = v___y_1863_;
v___y_1792_ = v___y_1864_;
v___y_1793_ = v___y_1865_;
goto v___jp_1789_;
}
}
}
v___jp_1866_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_IO_FS_writeFile(v___y_1869_, v___y_1873_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1869_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref_known(v___x_1874_, 1);
v___y_1861_ = v___y_1868_;
v___y_1862_ = v___y_1867_;
v___y_1863_ = v___y_1870_;
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___y_1871_;
goto v___jp_1860_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1879_ = lean_io_error_to_string(v_a_1875_);
v___x_1880_ = 3;
v___x_1881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*1, v___x_1880_);
lean_inc_ref(v___y_1871_);
v___x_1882_ = lean_apply_2(v___y_1871_, v___x_1881_, lean_box(0));
v___x_1883_ = lean_box(0);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1883_);
v___x_1885_ = v___x_1877_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
v___jp_1888_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1895_ = lean_box(v_tmp_1578_);
v___x_1896_ = lean_obj_tag_nat(v___x_1895_);
lean_dec(v___x_1895_);
v___x_1897_ = lean_unsigned_to_nat(4u);
v___x_1898_ = lean_nat_dec_eq(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = 1;
lean_inc_n(v___y_1890_, 2);
v___x_1900_ = l_Lean_Name_toString(v___y_1890_, v___x_1899_);
v___x_1901_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1900_, v___y_1890_);
lean_dec_ref(v___x_1900_);
v___y_1867_ = v___y_1890_;
v___y_1868_ = v___y_1889_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___y_1892_;
v___y_1871_ = v___y_1894_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___x_1901_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1902_; 
lean_inc(v___y_1890_);
v___x_1902_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1890_);
v___y_1867_ = v___y_1890_;
v___y_1868_ = v___y_1889_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___y_1892_;
v___y_1871_ = v___y_1894_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___x_1902_;
goto v___jp_1866_;
}
}
v___jp_1903_:
{
if (v_a_1911_ == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = l_IO_FS_createDirAll(v___y_1908_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec_ref_known(v___x_1912_, 1);
v___x_1913_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1914_ = l_IO_FS_writeFile(v___y_1906_, v___x_1913_);
lean_dec_ref(v___y_1906_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_dec_ref_known(v___x_1914_, 1);
v___y_1889_ = v___y_1905_;
v___y_1890_ = v___y_1904_;
v___y_1891_ = v___y_1907_;
v___y_1892_ = v___y_1909_;
v___y_1893_ = v___y_1910_;
v___y_1894_ = v_a_1575_;
goto v___jp_1888_;
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1927_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1927_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1919_ = lean_io_error_to_string(v_a_1915_);
v___x_1920_ = 3;
v___x_1921_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*1, v___x_1920_);
lean_inc_ref(v_a_1575_);
v___x_1922_ = lean_apply_2(v_a_1575_, v___x_1921_, lean_box(0));
v___x_1923_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1923_);
v___x_1925_ = v___x_1917_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1928_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1930_ = v___x_1912_;
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1912_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1940_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1932_ = lean_io_error_to_string(v_a_1928_);
v___x_1933_ = 3;
v___x_1934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1, v___x_1933_);
lean_inc_ref(v_a_1575_);
v___x_1935_ = lean_apply_2(v_a_1575_, v___x_1934_, lean_box(0));
v___x_1936_ = lean_box(0);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1936_);
v___x_1938_ = v___x_1930_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1906_);
v___y_1889_ = v___y_1905_;
v___y_1890_ = v___y_1904_;
v___y_1891_ = v___y_1907_;
v___y_1892_ = v___y_1909_;
v___y_1893_ = v___y_1910_;
v___y_1894_ = v_a_1575_;
goto v___jp_1888_;
}
}
v___jp_1944_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_inc(v___y_1949_);
lean_inc(v___y_1945_);
lean_inc(v_name_1577_);
v___x_1950_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1578_, v_lang_1579_, v_name_1577_, v___y_1945_, v___y_1949_);
v___x_1951_ = l_IO_FS_writeFile(v_configFile_1943_, v___x_1950_);
lean_dec_ref(v___x_1950_);
lean_dec_ref(v_configFile_1943_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_dec_ref_known(v___x_1951_, 1);
if (lean_obj_tag(v___y_1947_) == 1)
{
lean_object* v_val_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; uint8_t v___x_1959_; 
v_val_1952_ = lean_ctor_get(v___y_1947_, 0);
lean_inc_n(v_val_1952_, 2);
lean_dec_ref_known(v___y_1947_, 1);
v___x_1953_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1954_ = l_System_FilePath_withExtension(v_val_1952_, v___x_1953_);
v___x_1955_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1954_);
v___x_1956_ = l_Lake_joinRelative(v___x_1954_, v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1958_ = l_System_FilePath_pathExists(v___x_1956_);
v___x_1959_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1959_ == 0)
{
v___y_1904_ = v___y_1945_;
v___y_1905_ = v___y_1946_;
v___y_1906_ = v___x_1956_;
v___y_1907_ = v_val_1952_;
v___y_1908_ = v___x_1954_;
v___y_1909_ = v___y_1949_;
v___y_1910_ = v___y_1948_;
v_a_1911_ = v___x_1958_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v___x_1960_ = lean_box(0);
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1957_, v___x_1961_, v___x_1962_, v___x_1960_, v_a_1575_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
v___y_1904_ = v___y_1945_;
v___y_1905_ = v___y_1946_;
v___y_1906_ = v___x_1956_;
v___y_1907_ = v_val_1952_;
v___y_1908_ = v___x_1954_;
v___y_1909_ = v___y_1949_;
v___y_1910_ = v___y_1948_;
v_a_1911_ = v___x_1958_;
goto v___jp_1903_;
}
else
{
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1952_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_1963_;
}
}
}
else
{
lean_dec(v___y_1947_);
v___y_1861_ = v___y_1946_;
v___y_1862_ = v___y_1945_;
v___y_1863_ = v___y_1949_;
v___y_1864_ = v___y_1948_;
v___y_1865_ = v_a_1575_;
goto v___jp_1860_;
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_1964_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1966_ = v___x_1951_;
v_isShared_1967_ = v_isSharedCheck_1976_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1951_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1976_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1968_ = lean_io_error_to_string(v_a_1964_);
v___x_1969_ = 3;
v___x_1970_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*1, v___x_1969_);
lean_inc_ref(v_a_1575_);
v___x_1971_ = lean_apply_2(v_a_1575_, v___x_1970_, lean_box(0));
v___x_1972_ = lean_box(0);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1972_);
v___x_1974_ = v___x_1966_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
v___jp_1977_:
{
lean_object* v_lean_1980_; lean_object* v_toolchain_1981_; lean_object* v___x_1982_; 
v_lean_1980_ = lean_ctor_get(v_env_1580_, 1);
v_toolchain_1981_ = lean_ctor_get(v_env_1580_, 19);
lean_inc_ref(v_toolchain_1981_);
v___x_1982_ = l_Lake_ToolchainVer_ofString(v_toolchain_1981_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_ver_1983_; lean_object* v___x_1984_; 
v_ver_1983_ = lean_ctor_get(v___x_1982_, 1);
lean_inc_ref(v_ver_1983_);
lean_dec_ref_known(v___x_1982_, 2);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_ver_1983_);
lean_inc_ref(v_toolchain_1981_);
lean_inc_ref(v_lean_1980_);
v___y_1945_ = v_fst_1978_;
v___y_1946_ = v_lean_1980_;
v___y_1947_ = v_snd_1979_;
v___y_1948_ = v_toolchain_1981_;
v___y_1949_ = v___x_1984_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1985_; 
lean_dec_ref(v___x_1982_);
v___x_1985_ = lean_box(0);
lean_inc_ref(v_toolchain_1981_);
lean_inc_ref(v_lean_1980_);
v___y_1945_ = v_fst_1978_;
v___y_1946_ = v_lean_1980_;
v___y_1947_ = v_snd_1979_;
v___y_1948_ = v_toolchain_1981_;
v___y_1949_ = v___x_1985_;
goto v___jp_1944_;
}
}
v___jp_1986_:
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
lean_inc(v_name_1577_);
v_fst_1978_ = v_name_1577_;
v_snd_1979_ = v___x_1987_;
goto v___jp_1977_;
}
v___jp_1988_:
{
if (v_a_1991_ == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1989_);
v_fst_1978_ = v___y_1990_;
v_snd_1979_ = v___x_1992_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_1993_; 
lean_dec_ref(v___y_1989_);
v___x_1993_ = lean_box(0);
v_fst_1978_ = v___y_1990_;
v_snd_1979_ = v___x_1993_;
goto v___jp_1977_;
}
}
v___jp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1997_ = lean_box(v_tmp_1578_);
v___x_1998_ = lean_obj_tag_nat(v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_dec_eq(v___x_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
if (v_a_1996_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; uint8_t v___x_2005_; 
lean_inc(v_name_1577_);
v___x_2001_ = l_Lake_toUpperCamelCase(v_name_1577_);
lean_inc(v___x_2001_);
v___x_2002_ = l_Lean_modToFilePath(v_dir_1576_, v___x_2001_, v___y_1995_);
v___x_2003_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2004_ = l_System_FilePath_pathExists(v___x_2002_);
v___x_2005_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2005_ == 0)
{
v___y_1989_ = v___x_2002_;
v___y_1990_ = v___x_2001_;
v_a_1991_ = v___x_2004_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = lean_box(0);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2003_, v___x_2007_, v___x_2008_, v___x_2006_, v_a_1575_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_dec_ref_known(v___x_2009_, 1);
v___y_1989_ = v___x_2002_;
v___y_1990_ = v___x_2001_;
v_a_1991_ = v___x_2004_;
goto v___jp_1988_;
}
else
{
lean_dec_ref(v___x_2002_);
lean_dec(v___x_2001_);
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_2009_;
}
}
}
else
{
goto v___jp_1986_;
}
}
else
{
goto v___jp_1986_;
}
}
v___jp_2010_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; uint8_t v___x_2015_; 
v___x_2011_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_1577_);
v___x_2012_ = l_Lean_modToFilePath(v_dir_1576_, v_name_1577_, v___x_2011_);
v___x_2013_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2014_ = l_System_FilePath_pathExists(v___x_2012_);
lean_dec_ref(v___x_2012_);
v___x_2015_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2015_ == 0)
{
v___y_1995_ = v___x_2011_;
v_a_1996_ = v___x_2014_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2013_, v___x_2017_, v___x_2018_, v___x_2016_, v_a_1575_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_dec_ref_known(v___x_2019_, 1);
v___y_1995_ = v___x_2011_;
v_a_1996_ = v___x_2014_;
goto v___jp_1994_;
}
else
{
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_2019_;
}
}
}
v___jp_2020_:
{
if (v_a_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1576_);
v___x_2024_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1576_, v_tmp_1578_, v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 2);
v___x_2026_ = lean_array_get_size(v_a_2025_);
v___x_2027_ = lean_nat_dec_lt(v___x_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_a_2025_);
goto v___jp_2010_;
}
else
{
lean_object* v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = lean_usize_of_nat(v___x_2026_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2025_, v___x_2029_, v___x_2030_, v___x_2028_, v_a_1575_);
lean_dec(v_a_2025_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref_known(v___x_2031_, 1);
goto v___jp_2010_;
}
else
{
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v_a_2032_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2024_, 2);
v___x_2033_ = lean_array_get_size(v_a_2032_);
v___x_2034_ = lean_nat_dec_lt(v___x_2022_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_a_2032_);
v___x_2035_ = lean_box(0);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = lean_usize_of_nat(v___x_2033_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2032_, v___x_2038_, v___x_2039_, v___x_2037_, v_a_1575_);
lean_dec(v_a_2032_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2040_, 0);
lean_dec(v_unused_2048_);
v___x_2042_ = v___x_2040_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v___x_2040_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2037_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2037_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_configFile_1943_);
lean_dec_ref(v_env_1580_);
lean_dec(v_name_1577_);
lean_dec_ref(v_dir_1576_);
v___x_2049_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_1575_);
v___x_2050_ = lean_apply_2(v_a_1575_, v___x_2049_, lean_box(0));
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2060_, lean_object* v_dir_2061_, lean_object* v_name_2062_, lean_object* v_tmp_2063_, lean_object* v_lang_2064_, lean_object* v_env_2065_, lean_object* v_offline_2066_, lean_object* v_a_2067_){
_start:
{
uint8_t v_tmp_boxed_2068_; uint8_t v_lang_boxed_2069_; uint8_t v_offline_boxed_2070_; lean_object* v_res_2071_; 
v_tmp_boxed_2068_ = lean_unbox(v_tmp_2063_);
v_lang_boxed_2069_ = lean_unbox(v_lang_2064_);
v_offline_boxed_2070_ = lean_unbox(v_offline_2066_);
v_res_2071_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2060_, v_dir_2061_, v_name_2062_, v_tmp_boxed_2068_, v_lang_boxed_2069_, v_env_2065_, v_offline_boxed_2070_);
lean_dec_ref(v_a_2060_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2073_, uint8_t v_tmp_2074_, uint8_t v_lang_2075_, lean_object* v_env_2076_, lean_object* v_cwd_2077_, uint8_t v_offline_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___y_2082_; lean_object* v_a_2100_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2136_ = lean_string_dec_eq(v_name_2073_, v___x_2135_);
if (v___x_2136_ == 0)
{
v_a_2100_ = v_name_2073_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v_name_2073_);
lean_inc_ref(v_cwd_2077_);
v___x_2137_ = lean_io_realpath(v_cwd_2077_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2155_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2155_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2155_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
lean_inc(v_a_2138_);
v___x_2142_ = l_System_FilePath_fileName(v_a_2138_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec_ref(v_cwd_2077_);
lean_dec_ref(v_env_2076_);
v___x_2143_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2144_ = lean_string_append(v___x_2143_, v_a_2138_);
lean_dec(v_a_2138_);
v___x_2145_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2146_ = lean_string_append(v___x_2144_, v___x_2145_);
v___x_2147_ = 3;
v___x_2148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*1, v___x_2147_);
lean_inc_ref(v_a_2079_);
v___x_2149_ = lean_apply_2(v_a_2079_, v___x_2148_, lean_box(0));
v___x_2150_ = lean_box(0);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 1);
lean_ctor_set(v___x_2140_, 0, v___x_2150_);
v___x_2152_ = v___x_2140_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
else
{
lean_object* v_val_2154_; 
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
v_val_2154_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v___x_2142_, 1);
v_a_2100_ = v_val_2154_;
goto v___jp_2099_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v_cwd_2077_);
lean_dec_ref(v_env_2076_);
v_a_2156_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2158_ = v___x_2137_;
v_isShared_2159_ = v_isSharedCheck_2168_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2137_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2168_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2160_ = lean_io_error_to_string(v_a_2156_);
v___x_2161_ = 3;
v___x_2162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___x_2161_);
lean_inc_ref(v_a_2079_);
v___x_2163_ = lean_apply_2(v_a_2079_, v___x_2162_, lean_box(0));
v___x_2164_ = lean_box(0);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2164_);
v___x_2166_ = v___x_2158_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; 
lean_inc_ref(v_cwd_2077_);
v___x_2083_ = l_IO_FS_createDirAll(v_cwd_2077_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = l_Lake_stringToLegalOrSimpleName(v___y_2082_);
v___x_2085_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2079_, v_cwd_2077_, v___x_2084_, v_tmp_2074_, v_lang_2075_, v_env_2076_, v_offline_2078_);
return v___x_2085_;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_cwd_2077_);
lean_dec_ref(v_env_2076_);
v_a_2086_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2088_ = v___x_2083_;
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2083_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2090_ = lean_io_error_to_string(v_a_2086_);
v___x_2091_ = 3;
v___x_2092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*1, v___x_2091_);
lean_inc_ref(v_a_2079_);
v___x_2093_ = lean_apply_2(v_a_2079_, v___x_2092_, lean_box(0));
v___x_2094_ = lean_box(0);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2094_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_str_2105_; lean_object* v_startInclusive_2106_; lean_object* v_endExclusive_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_string_utf8_byte_size(v_a_2100_);
v___x_2103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2103_, 0, v_a_2100_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2102_);
v___x_2104_ = l_String_Slice_trimAscii(v___x_2103_);
v_str_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_ref(v_str_2105_);
v_startInclusive_2106_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_startInclusive_2106_);
v_endExclusive_2107_ = lean_ctor_get(v___x_2104_, 2);
lean_inc(v_endExclusive_2107_);
lean_dec_ref(v___x_2104_);
v___x_2108_ = lean_string_utf8_extract_fast(v_str_2105_, v_startInclusive_2106_, v_endExclusive_2107_);
lean_dec(v_endExclusive_2107_);
lean_dec(v_startInclusive_2106_);
lean_dec_ref(v_str_2105_);
v___x_2109_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2108_);
v___x_2110_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2108_, v___x_2109_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 2);
v___x_2112_ = lean_array_get_size(v_a_2111_);
v___x_2113_ = lean_nat_dec_lt(v___x_2101_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec(v_a_2111_);
v___y_2082_ = v___x_2108_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_box(0);
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = lean_usize_of_nat(v___x_2112_);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2111_, v___x_2115_, v___x_2116_, v___x_2114_, v_a_2079_);
lean_dec(v_a_2111_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref_known(v___x_2117_, 1);
v___y_2082_ = v___x_2108_;
goto v___jp_2081_;
}
else
{
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_cwd_2077_);
lean_dec_ref(v_env_2076_);
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_cwd_2077_);
lean_dec_ref(v_env_2076_);
v_a_2118_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2110_, 2);
v___x_2119_ = lean_array_get_size(v_a_2118_);
v___x_2120_ = lean_nat_dec_lt(v___x_2101_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v_a_2118_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = lean_usize_of_nat(v___x_2119_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2118_, v___x_2124_, v___x_2125_, v___x_2123_, v_a_2079_);
lean_dec(v_a_2118_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2126_, 0);
lean_dec(v_unused_2134_);
v___x_2128_ = v___x_2126_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2126_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2123_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2123_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
return v___x_2126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2169_, lean_object* v_tmp_2170_, lean_object* v_lang_2171_, lean_object* v_env_2172_, lean_object* v_cwd_2173_, lean_object* v_offline_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
uint8_t v_tmp_boxed_2177_; uint8_t v_lang_boxed_2178_; uint8_t v_offline_boxed_2179_; lean_object* v_res_2180_; 
v_tmp_boxed_2177_ = lean_unbox(v_tmp_2170_);
v_lang_boxed_2178_ = lean_unbox(v_lang_2171_);
v_offline_boxed_2179_ = lean_unbox(v_offline_2174_);
v_res_2180_ = l_Lake_init(v_name_2169_, v_tmp_boxed_2177_, v_lang_boxed_2178_, v_env_2172_, v_cwd_2173_, v_offline_boxed_2179_, v_a_2175_);
lean_dec_ref(v_a_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2181_, uint8_t v_tmp_2182_, uint8_t v_lang_2183_, lean_object* v_env_2184_, lean_object* v_cwd_2185_, uint8_t v_offline_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_str_2193_; lean_object* v_startInclusive_2194_; lean_object* v_endExclusive_2195_; lean_object* v_name_2196_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_string_utf8_byte_size(v_name_2181_);
v___x_2191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2191_, 0, v_name_2181_);
lean_ctor_set(v___x_2191_, 1, v___x_2189_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
v___x_2192_ = l_String_Slice_trimAscii(v___x_2191_);
v_str_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_str_2193_);
v_startInclusive_2194_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_startInclusive_2194_);
v_endExclusive_2195_ = lean_ctor_get(v___x_2192_, 2);
lean_inc(v_endExclusive_2195_);
lean_dec_ref(v___x_2192_);
v_name_2196_ = lean_string_utf8_extract_fast(v_str_2193_, v_startInclusive_2194_, v_endExclusive_2195_);
lean_dec(v_endExclusive_2195_);
lean_dec(v_startInclusive_2194_);
lean_dec_ref(v_str_2193_);
v___x_2216_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2196_);
v___x_2217_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2196_, v___x_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 2);
v___x_2219_ = lean_array_get_size(v_a_2218_);
v___x_2220_ = lean_nat_dec_lt(v___x_2189_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_dec(v_a_2218_);
goto v___jp_2197_;
}
else
{
lean_object* v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = lean_usize_of_nat(v___x_2219_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2218_, v___x_2222_, v___x_2223_, v___x_2221_, v_a_2187_);
lean_dec(v_a_2218_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_dec_ref_known(v___x_2224_, 1);
goto v___jp_2197_;
}
else
{
lean_dec_ref(v_name_2196_);
lean_dec_ref(v_cwd_2185_);
lean_dec_ref(v_env_2184_);
return v___x_2224_;
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
lean_dec_ref(v_name_2196_);
lean_dec_ref(v_cwd_2185_);
lean_dec_ref(v_env_2184_);
v_a_2225_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2217_, 2);
v___x_2226_ = lean_array_get_size(v_a_2225_);
v___x_2227_ = lean_nat_dec_lt(v___x_2189_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v_a_2225_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2226_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2225_, v___x_2231_, v___x_2232_, v___x_2230_, v_a_2187_);
lean_dec(v_a_2225_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2241_);
v___x_2235_ = v___x_2233_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v___x_2233_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set_tag(v___x_2235_, 1);
lean_ctor_set(v___x_2235_, 0, v___x_2230_);
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2230_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
return v___x_2233_;
}
}
}
v___jp_2197_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = l_Lake_stringToLegalOrSimpleName(v_name_2196_);
lean_inc(v___x_2198_);
v___x_2199_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2198_);
v___x_2200_ = l_Lake_joinRelative(v_cwd_2185_, v___x_2199_);
lean_inc_ref(v___x_2200_);
v___x_2201_ = l_IO_FS_createDirAll(v___x_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref_known(v___x_2201_, 1);
v___x_2202_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2187_, v___x_2200_, v___x_2198_, v_tmp_2182_, v_lang_2183_, v_env_2184_, v_offline_2186_);
return v___x_2202_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___x_2200_);
lean_dec(v___x_2198_);
lean_dec_ref(v_env_2184_);
v_a_2203_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2205_ = v___x_2201_;
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2201_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2207_ = lean_io_error_to_string(v_a_2203_);
v___x_2208_ = 3;
v___x_2209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*1, v___x_2208_);
lean_inc_ref(v_a_2187_);
v___x_2210_ = lean_apply_2(v_a_2187_, v___x_2209_, lean_box(0));
v___x_2211_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2211_);
v___x_2213_ = v___x_2205_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2242_, lean_object* v_tmp_2243_, lean_object* v_lang_2244_, lean_object* v_env_2245_, lean_object* v_cwd_2246_, lean_object* v_offline_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
uint8_t v_tmp_boxed_2250_; uint8_t v_lang_boxed_2251_; uint8_t v_offline_boxed_2252_; lean_object* v_res_2253_; 
v_tmp_boxed_2250_ = lean_unbox(v_tmp_2243_);
v_lang_boxed_2251_ = lean_unbox(v_lang_2244_);
v_offline_boxed_2252_ = lean_unbox(v_offline_2247_);
v_res_2253_ = l_Lake_new(v_name_2242_, v_tmp_boxed_2250_, v_lang_boxed_2251_, v_env_2245_, v_cwd_2246_, v_offline_boxed_2252_, v_a_2248_);
lean_dec_ref(v_a_2248_);
return v_res_2253_;
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

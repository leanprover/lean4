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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
extern uint32_t l_Lean_idEndEscape;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_Git_upstreamBranch;
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 201, .m_capacity = 201, .m_length = 200, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 488, .m_capacity = 488, .m_length = 487, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1951, .m_capacity = 1951, .m_length = 1950, .m_data = "name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 428, .m_capacity = 428, .m_length = 427, .m_data = "name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "create-release.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created Mathlib update CI workflow at '"};
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to initialize git repository"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Basic.lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "package already initialized"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "illegal package name '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "reserved package name"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t v_x_332_){
_start:
{
switch(v_x_332_)
{
case 0:
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
return v___x_333_;
}
case 1:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(1u);
return v___x_334_;
}
case 2:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(2u);
return v___x_335_;
}
case 3:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(3u);
return v___x_336_;
}
default: 
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(4u);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_x_boxed_339_; lean_object* v_res_340_; 
v_x_boxed_339_ = lean_unbox(v_x_338_);
v_res_340_ = l_Lake_InitTemplate_ctorIdx(v_x_boxed_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lake_InitTemplate_ctorIdx(v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object* v_x_343_){
_start:
{
uint8_t v_x_4__boxed_344_; lean_object* v_res_345_; 
v_x_4__boxed_344_ = lean_unbox(v_x_343_);
v_res_345_ = l_Lake_InitTemplate_toCtorIdx(v_x_4__boxed_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* v_k_346_){
_start:
{
lean_inc(v_k_346_);
return v_k_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_347_);
lean_dec(v_k_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* v_motive_349_, lean_object* v_ctorIdx_350_, uint8_t v_t_351_, lean_object* v_h_352_, lean_object* v_k_353_){
_start:
{
lean_inc(v_k_353_);
return v_k_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* v_motive_354_, lean_object* v_ctorIdx_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_k_358_){
_start:
{
uint8_t v_t_boxed_359_; lean_object* v_res_360_; 
v_t_boxed_359_ = lean_unbox(v_t_356_);
v_res_360_ = l_Lake_InitTemplate_ctorElim(v_motive_354_, v_ctorIdx_355_, v_t_boxed_359_, v_h_357_, v_k_358_);
lean_dec(v_k_358_);
lean_dec(v_ctorIdx_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* v_std_361_){
_start:
{
lean_inc(v_std_361_);
return v_std_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* v_std_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_InitTemplate_std_elim___redArg(v_std_362_);
lean_dec(v_std_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* v_motive_364_, uint8_t v_t_365_, lean_object* v_h_366_, lean_object* v_std_367_){
_start:
{
lean_inc(v_std_367_);
return v_std_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* v_motive_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_std_371_){
_start:
{
uint8_t v_t_boxed_372_; lean_object* v_res_373_; 
v_t_boxed_372_ = lean_unbox(v_t_369_);
v_res_373_ = l_Lake_InitTemplate_std_elim(v_motive_368_, v_t_boxed_372_, v_h_370_, v_std_371_);
lean_dec(v_std_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* v_exe_374_){
_start:
{
lean_inc(v_exe_374_);
return v_exe_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* v_exe_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_375_);
lean_dec(v_exe_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* v_motive_377_, uint8_t v_t_378_, lean_object* v_h_379_, lean_object* v_exe_380_){
_start:
{
lean_inc(v_exe_380_);
return v_exe_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* v_motive_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_exe_384_){
_start:
{
uint8_t v_t_boxed_385_; lean_object* v_res_386_; 
v_t_boxed_385_ = lean_unbox(v_t_382_);
v_res_386_ = l_Lake_InitTemplate_exe_elim(v_motive_381_, v_t_boxed_385_, v_h_383_, v_exe_384_);
lean_dec(v_exe_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* v_lib_387_){
_start:
{
lean_inc(v_lib_387_);
return v_lib_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* v_lib_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_388_);
lean_dec(v_lib_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* v_motive_390_, uint8_t v_t_391_, lean_object* v_h_392_, lean_object* v_lib_393_){
_start:
{
lean_inc(v_lib_393_);
return v_lib_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* v_motive_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_lib_397_){
_start:
{
uint8_t v_t_boxed_398_; lean_object* v_res_399_; 
v_t_boxed_398_ = lean_unbox(v_t_395_);
v_res_399_ = l_Lake_InitTemplate_lib_elim(v_motive_394_, v_t_boxed_398_, v_h_396_, v_lib_397_);
lean_dec(v_lib_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* v_mathLax_400_){
_start:
{
lean_inc(v_mathLax_400_);
return v_mathLax_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* v_mathLax_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_401_);
lean_dec(v_mathLax_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* v_motive_403_, uint8_t v_t_404_, lean_object* v_h_405_, lean_object* v_mathLax_406_){
_start:
{
lean_inc(v_mathLax_406_);
return v_mathLax_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_mathLax_410_){
_start:
{
uint8_t v_t_boxed_411_; lean_object* v_res_412_; 
v_t_boxed_411_ = lean_unbox(v_t_408_);
v_res_412_ = l_Lake_InitTemplate_mathLax_elim(v_motive_407_, v_t_boxed_411_, v_h_409_, v_mathLax_410_);
lean_dec(v_mathLax_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* v_math_413_){
_start:
{
lean_inc(v_math_413_);
return v_math_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* v_math_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_InitTemplate_math_elim___redArg(v_math_414_);
lean_dec(v_math_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* v_motive_416_, uint8_t v_t_417_, lean_object* v_h_418_, lean_object* v_math_419_){
_start:
{
lean_inc(v_math_419_);
return v_math_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_math_423_){
_start:
{
uint8_t v_t_boxed_424_; lean_object* v_res_425_; 
v_t_boxed_424_ = lean_unbox(v_t_421_);
v_res_425_ = l_Lake_InitTemplate_math_elim(v_motive_420_, v_t_boxed_424_, v_h_422_, v_math_423_);
lean_dec(v_math_423_);
return v_res_425_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(2u);
v___x_442_ = lean_nat_to_int(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_to_int(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t v_x_445_, lean_object* v_prec_446_){
_start:
{
lean_object* v___y_448_; lean_object* v___y_455_; lean_object* v___y_462_; lean_object* v___y_469_; lean_object* v___y_476_; 
switch(v_x_445_)
{
case 0:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1024u);
v___x_483_ = lean_nat_dec_le(v___x_482_, v_prec_446_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_448_ = v___x_484_;
goto v___jp_447_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_448_ = v___x_485_;
goto v___jp_447_;
}
}
case 1:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1024u);
v___x_487_ = lean_nat_dec_le(v___x_486_, v_prec_446_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_455_ = v___x_488_;
goto v___jp_454_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_455_ = v___x_489_;
goto v___jp_454_;
}
}
case 2:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1024u);
v___x_491_ = lean_nat_dec_le(v___x_490_, v_prec_446_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_462_ = v___x_492_;
goto v___jp_461_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_462_ = v___x_493_;
goto v___jp_461_;
}
}
case 3:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(1024u);
v___x_495_ = lean_nat_dec_le(v___x_494_, v_prec_446_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
v___x_496_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_469_ = v___x_496_;
goto v___jp_468_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_469_ = v___x_497_;
goto v___jp_468_;
}
}
default: 
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(1024u);
v___x_499_ = lean_nat_dec_le(v___x_498_, v_prec_446_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_476_ = v___x_500_;
goto v___jp_475_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_476_ = v___x_501_;
goto v___jp_475_;
}
}
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
v___x_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = 0;
v___x_452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*1, v___x_451_);
v___x_453_ = l_Repr_addAppParen(v___x_452_, v_prec_446_);
return v___x_453_;
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
v___x_457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_457_, 0, v___y_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = 0;
v___x_459_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*1, v___x_458_);
v___x_460_ = l_Repr_addAppParen(v___x_459_, v_prec_446_);
return v___x_460_;
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
v___x_467_ = l_Repr_addAppParen(v___x_466_, v_prec_446_);
return v___x_467_;
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
v___x_471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = 0;
v___x_473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
v___x_474_ = l_Repr_addAppParen(v___x_473_, v_prec_446_);
return v___x_474_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
v___x_478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = 0;
v___x_480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_479_);
v___x_481_ = l_Repr_addAppParen(v___x_480_, v_prec_446_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* v_x_502_, lean_object* v_prec_503_){
_start:
{
uint8_t v_x_289__boxed_504_; lean_object* v_res_505_; 
v_x_289__boxed_504_ = lean_unbox(v_x_502_);
v_res_505_ = l_Lake_instReprInitTemplate_repr(v_x_289__boxed_504_, v_prec_503_);
lean_dec(v_prec_503_);
return v_res_505_;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* v_n_508_){
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* v_n_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Lake_InitTemplate_ofNat(v_n_522_);
lean_dec(v_n_522_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t v_x_525_, uint8_t v_y_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = l_Lake_InitTemplate_ctorIdx(v_x_525_);
v___x_528_ = l_Lake_InitTemplate_ctorIdx(v_y_526_);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
lean_dec(v___x_528_);
lean_dec(v___x_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* v_x_530_, lean_object* v_y_531_){
_start:
{
uint8_t v_x_13__boxed_532_; uint8_t v_y_14__boxed_533_; uint8_t v_res_534_; lean_object* v_r_535_; 
v_x_13__boxed_532_ = lean_unbox(v_x_530_);
v_y_14__boxed_533_ = lean_unbox(v_y_531_);
v_res_534_ = l_Lake_instDecidableEqInitTemplate(v_x_13__boxed_532_, v_y_14__boxed_533_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = 0;
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
v___x_559_ = lean_string_dec_eq(v_x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
v___x_561_ = lean_string_dec_eq(v_x_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
v___x_563_ = lean_string_dec_eq(v_x_557_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
v___x_565_ = lean_string_dec_eq(v_x_557_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
v___x_567_ = lean_string_dec_eq(v_x_557_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_box(0);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return v___x_571_;
}
}
else
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lake_InitTemplate_ofString_x3f(v_x_574_);
lean_dec_ref(v_x_574_);
return v_res_575_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void){
_start:
{
uint32_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = l_Lean_idBeginEscape;
v___x_578_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_579_ = lean_string_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void){
_start:
{
uint32_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = l_Lean_idEndEscape;
v___x_581_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_582_ = lean_string_push(v___x_581_, v___x_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* v_id_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
v___x_585_ = lean_string_append(v___x_584_, v_id_583_);
v___x_586_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* v_id_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_588_);
lean_dec_ref(v_id_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* v_msg_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_592_ = lean_panic_fn(v___x_591_, v_msg_590_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_597_ = lean_unsigned_to_nat(23u);
v___x_598_ = lean_unsigned_to_nat(350u);
v___x_599_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_600_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_601_ = l_mkPanicMessageWithDecl(v___x_600_, v___x_599_, v___x_598_, v___x_597_, v___x_596_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_604_ = lean_unsigned_to_nat(23u);
v___x_605_ = lean_unsigned_to_nat(353u);
v___x_606_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_607_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* v_x_609_){
_start:
{
switch(lean_obj_tag(v_x_609_))
{
case 0:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
v___x_611_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_610_);
return v___x_611_;
}
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_x_609_, 0);
if (lean_obj_tag(v_pre_612_) == 0)
{
lean_object* v_str_613_; lean_object* v___x_614_; 
v_str_613_ = lean_ctor_get(v_x_609_, 1);
v___x_614_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_613_);
return v___x_614_;
}
else
{
lean_object* v_str_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_str_615_ = lean_ctor_get(v_x_609_, 1);
v___x_616_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_612_);
v___x_617_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_618_ = lean_string_append(v___x_616_, v___x_617_);
v___x_619_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_615_);
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
lean_dec_ref(v___x_619_);
return v___x_620_;
}
}
default: 
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
v___x_622_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_621_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* v_s_625_, lean_object* v_p_626_){
_start:
{
uint32_t v___y_628_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_string_utf8_byte_size(v_s_625_);
v___x_634_ = lean_nat_dec_eq(v_p_626_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_string_utf8_get_fast(v_s_625_, v_p_626_);
v___x_636_ = 46;
v___x_637_ = lean_uint32_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
v___y_628_ = v___x_635_;
goto v___jp_627_;
}
else
{
uint32_t v___x_638_; 
v___x_638_ = 45;
v___y_628_ = v___x_638_;
goto v___jp_627_;
}
}
else
{
lean_dec(v_p_626_);
return v_s_625_;
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc(v_p_626_);
v___x_629_ = lean_string_utf8_set(v_s_625_, v_p_626_, v___y_628_);
v___x_630_ = l_Char_utf8Size(v___y_628_);
v___x_631_ = lean_nat_add(v_p_626_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v_p_626_);
v_s_625_ = v___x_629_;
v_p_626_ = v___x_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* v_name_639_){
_start:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = 0;
v___x_641_ = l_Lean_Name_toString(v_name_639_, v___x_640_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(v___x_641_, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* v_s_644_, lean_object* v_p_645_){
_start:
{
uint32_t v___y_647_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_string_utf8_byte_size(v_s_644_);
v___x_653_ = lean_nat_dec_eq(v_p_645_, v___x_652_);
if (v___x_653_ == 0)
{
uint32_t v___x_654_; uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_string_utf8_get_fast(v_s_644_, v_p_645_);
v___x_655_ = 65;
v___x_656_ = lean_uint32_dec_le(v___x_655_, v___x_654_);
if (v___x_656_ == 0)
{
v___y_647_ = v___x_654_;
goto v___jp_646_;
}
else
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 90;
v___x_658_ = lean_uint32_dec_le(v___x_654_, v___x_657_);
if (v___x_658_ == 0)
{
v___y_647_ = v___x_654_;
goto v___jp_646_;
}
else
{
uint32_t v___x_659_; uint32_t v___x_660_; 
v___x_659_ = 32;
v___x_660_ = lean_uint32_add(v___x_654_, v___x_659_);
v___y_647_ = v___x_660_;
goto v___jp_646_;
}
}
}
else
{
lean_dec(v_p_645_);
return v_s_644_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_inc(v_p_645_);
v___x_648_ = lean_string_utf8_set(v_s_644_, v_p_645_, v___y_647_);
v___x_649_ = l_Char_utf8Size(v___y_647_);
v___x_650_ = lean_nat_add(v_p_645_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v_p_645_);
v_s_644_ = v___x_648_;
v_p_645_ = v___x_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_663_, uint8_t v_lang_664_, lean_object* v_pkgName_665_, lean_object* v_root_666_, lean_object* v_leanVer_x3f_667_){
_start:
{
lean_object* v_pkgNameStr_668_; lean_object* v___y_670_; 
v_pkgNameStr_668_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_665_);
if (lean_obj_tag(v_leanVer_x3f_667_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_670_ = v___x_701_;
goto v___jp_669_;
}
else
{
lean_object* v_val_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_val_702_ = lean_ctor_get(v_leanVer_x3f_667_, 0);
lean_inc(v_val_702_);
lean_dec_ref(v_leanVer_x3f_667_);
v___x_703_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_704_ = l_Lake_StdVer_toString(v_val_702_);
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
lean_dec_ref(v___x_704_);
v___y_670_ = v___x_705_;
goto v___jp_669_;
}
v___jp_669_:
{
switch(v_tmp_663_)
{
case 0:
{
lean_dec_ref(v___y_670_);
if (v_lang_664_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_666_);
lean_dec(v_root_666_);
v___x_672_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_668_);
v___x_673_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_668_, v___x_672_);
v___x_674_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_668_, v___x_671_, v___x_673_);
lean_dec_ref(v___x_671_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_675_ = 1;
v___x_676_ = l_Lean_Name_toString(v_root_666_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_668_);
v___x_678_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_668_, v___x_677_);
v___x_679_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_668_, v___x_676_, v___x_678_);
return v___x_679_;
}
}
case 1:
{
lean_dec_ref(v___y_670_);
lean_dec(v_root_666_);
if (v_lang_664_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_668_);
v___x_681_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_668_, v___x_680_);
v___x_682_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_668_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_668_);
v___x_684_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_668_, v___x_683_);
v___x_685_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_668_, v___x_684_);
return v___x_685_;
}
}
case 2:
{
lean_dec_ref(v___y_670_);
if (v_lang_664_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_666_);
lean_dec(v_root_666_);
v___x_687_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_668_, v___x_686_);
lean_dec_ref(v___x_686_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = 1;
v___x_689_ = l_Lean_Name_toString(v_root_666_, v___x_688_);
v___x_690_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_668_, v___x_689_);
return v___x_690_;
}
}
case 3:
{
if (v_lang_664_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_666_);
lean_dec(v_root_666_);
v___x_692_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_668_, v___x_691_, v___y_670_);
lean_dec_ref(v___x_691_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = 1;
v___x_694_ = l_Lean_Name_toString(v_root_666_, v___x_693_);
v___x_695_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_668_, v___x_694_, v___y_670_);
return v___x_695_;
}
}
default: 
{
if (v_lang_664_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_666_);
lean_dec(v_root_666_);
v___x_697_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_668_, v___x_696_, v___y_670_);
lean_dec_ref(v___x_696_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = 1;
v___x_699_ = l_Lean_Name_toString(v_root_666_, v___x_698_);
v___x_700_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_668_, v___x_699_, v___y_670_);
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_706_, lean_object* v_lang_707_, lean_object* v_pkgName_708_, lean_object* v_root_709_, lean_object* v_leanVer_x3f_710_){
_start:
{
uint8_t v_tmp_boxed_711_; uint8_t v_lang_boxed_712_; lean_object* v_res_713_; 
v_tmp_boxed_711_ = lean_unbox(v_tmp_706_);
v_lang_boxed_712_ = lean_unbox(v_lang_707_);
v_res_713_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_711_, v_lang_boxed_712_, v_pkgName_708_, v_root_709_, v_leanVer_x3f_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_739_, uint8_t v_tmp_740_, lean_object* v_a_741_){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_743_ = 0;
v___x_744_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_745_ = lean_array_push(v_a_741_, v___x_744_);
v___x_746_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_747_ = l_Lake_joinRelative(v_dir_739_, v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_749_ = l_Lake_joinRelative(v___x_747_, v___x_748_);
lean_inc_ref(v___x_749_);
v___x_750_ = l_IO_FS_createDirAll(v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___y_754_; uint8_t v___x_809_; 
lean_dec_ref(v___x_750_);
v___x_751_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_749_);
v___x_752_ = l_Lake_joinRelative(v___x_749_, v___x_751_);
v___x_809_ = l_System_FilePath_pathExists(v___x_752_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; uint8_t v___x_811_; 
v___x_810_ = 4;
v___x_811_ = l_Lake_instDecidableEqInitTemplate(v_tmp_740_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_813_ = l_IO_FS_writeFile(v___x_752_, v___x_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_dec_ref(v___x_813_);
v___y_754_ = v___x_745_;
goto v___jp_753_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v___x_752_);
lean_dec_ref(v___x_749_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_io_error_to_string(v_a_814_);
v___x_816_ = 3;
v___x_817_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*1, v___x_816_);
v___x_818_ = lean_array_get_size(v___x_745_);
v___x_819_ = lean_array_push(v___x_745_, v___x_817_);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
return v___x_820_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_822_ = l_IO_FS_writeFile(v___x_752_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref(v___x_822_);
v___y_754_ = v___x_745_;
goto v___jp_753_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___x_752_);
lean_dec_ref(v___x_749_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_822_);
v___x_824_ = lean_io_error_to_string(v_a_823_);
v___x_825_ = 3;
v___x_826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*1, v___x_825_);
v___x_827_ = lean_array_get_size(v___x_745_);
v___x_828_ = lean_array_push(v___x_745_, v___x_826_);
v___x_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
return v___x_829_;
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_752_);
lean_dec_ref(v___x_749_);
v___x_830_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
v___x_831_ = lean_array_push(v___x_745_, v___x_830_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; uint8_t v___x_762_; 
v___x_755_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_756_ = lean_string_append(v___x_755_, v___x_752_);
lean_dec_ref(v___x_752_);
v___x_757_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_758_ = lean_string_append(v___x_756_, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*1, v___x_743_);
v___x_760_ = lean_array_push(v___y_754_, v___x_759_);
v___x_761_ = 4;
v___x_762_ = l_Lake_instDecidableEqInitTemplate(v_tmp_740_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_749_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(v___x_749_);
v___x_766_ = l_Lake_joinRelative(v___x_749_, v___x_765_);
v___x_767_ = l_System_FilePath_pathExists(v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_769_ = l_IO_FS_writeFile(v___x_766_, v___x_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref(v___x_769_);
v___x_770_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
v___x_771_ = l_Lake_joinRelative(v___x_749_, v___x_770_);
v___x_772_ = l_System_FilePath_pathExists(v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_774_ = lean_string_append(v___x_773_, v___x_766_);
lean_dec_ref(v___x_766_);
v___x_775_ = lean_string_append(v___x_774_, v___x_757_);
v___x_776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*1, v___x_743_);
v___x_777_ = lean_array_push(v___x_760_, v___x_776_);
if (v___x_772_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_779_ = l_IO_FS_writeFile(v___x_771_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref(v___x_779_);
v___x_780_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_781_ = lean_string_append(v___x_780_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_782_ = lean_string_append(v___x_781_, v___x_757_);
v___x_783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v___x_743_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_array_push(v___x_777_, v___x_783_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v___x_771_);
v_a_787_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_779_);
v___x_788_ = lean_io_error_to_string(v_a_787_);
v___x_789_ = 3;
v___x_790_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*1, v___x_789_);
v___x_791_ = lean_array_get_size(v___x_777_);
v___x_792_ = lean_array_push(v___x_777_, v___x_790_);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_771_);
v___x_794_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
v___x_795_ = lean_array_push(v___x_777_, v___x_794_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
return v___x_797_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v___x_766_);
lean_dec_ref(v___x_749_);
v_a_798_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_769_);
v___x_799_ = lean_io_error_to_string(v_a_798_);
v___x_800_ = 3;
v___x_801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*1, v___x_800_);
v___x_802_ = lean_array_get_size(v___x_760_);
v___x_803_ = lean_array_push(v___x_760_, v___x_801_);
v___x_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v___x_766_);
lean_dec_ref(v___x_749_);
v___x_805_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
v___x_806_ = lean_array_push(v___x_760_, v___x_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v___x_749_);
v_a_834_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_750_);
v___x_835_ = lean_io_error_to_string(v_a_834_);
v___x_836_ = 3;
v___x_837_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*1, v___x_836_);
v___x_838_ = lean_array_get_size(v___x_745_);
v___x_839_ = lean_array_push(v___x_745_, v___x_837_);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_841_, lean_object* v_tmp_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
uint8_t v_tmp_boxed_845_; lean_object* v_res_846_; 
v_tmp_boxed_845_ = lean_unbox(v_tmp_842_);
v_res_846_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_841_, v_tmp_boxed_845_, v_a_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_apply_2(v___y_848_, v___y_847_, lean_box(0));
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(v___y_852_, v___y_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(v___y_857_, v___y_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object* v_x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(v_x_861_, v___y_862_, v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_apply_2(v___y_866_, v___y_867_, lean_box(0));
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg___boxed(lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(v___y_871_, v___y_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(lean_object* v_as_875_, size_t v_i_876_, size_t v_stop_877_, lean_object* v_b_878_, lean_object* v___y_879_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_eq(v_i_876_, v_stop_877_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_array_uget_borrowed(v_as_875_, v_i_876_);
lean_inc(v___x_882_);
lean_inc_ref(v___y_879_);
v___x_883_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(v___y_879_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; size_t v___x_885_; size_t v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_876_, v___x_885_);
v_i_876_ = v___x_886_;
v_b_878_ = v_a_884_;
goto _start;
}
else
{
lean_dec_ref(v___y_879_);
return v___x_883_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec_ref(v___y_879_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_b_878_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1___boxed(lean_object* v_as_889_, lean_object* v_i_890_, lean_object* v_stop_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_i_boxed_895_; size_t v_stop_boxed_896_; lean_object* v_res_897_; 
v_i_boxed_895_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_stop_boxed_896_ = lean_unbox_usize(v_stop_891_);
lean_dec(v_stop_891_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_as_889_, v_i_boxed_895_, v_stop_boxed_896_, v_b_892_, v___y_893_);
lean_dec_ref(v_as_889_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_912_ = lean_array_get_size(v___x_911_);
return v___x_912_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_nat_dec_lt(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_917_ = lean_nat_dec_le(v___x_916_, v___x_916_);
return v___x_917_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10(void){
_start:
{
lean_object* v___x_918_; size_t v___x_919_; 
v___x_918_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_919_ = lean_usize_of_nat(v___x_918_);
return v___x_919_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_924_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_925_ = l_Lake_Git_upstreamBranch;
v___x_926_ = lean_string_dec_eq(v___x_925_, v___x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_934_, lean_object* v_name_935_, uint8_t v_tmp_936_, uint8_t v_lang_937_, lean_object* v_env_938_, uint8_t v_offline_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_945_; lean_object* v___y_947_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v_a_976_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; uint8_t v_a_1108_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v_a_1177_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v_a_1209_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; uint8_t v_a_1310_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_configFile_1342_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v_a_1392_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v_a_1416_; lean_object* v___y_1434_; uint8_t v___x_1435_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_945_ = l_Lake_defaultConfigFile;
v___x_1340_ = l_Lake_ConfigLang_fileExtension(v_lang_937_);
v___x_1341_ = l_System_FilePath_addExtension(v___x_945_, v___x_1340_);
lean_dec_ref(v___x_1340_);
lean_inc_ref(v_dir_934_);
v_configFile_1342_ = l_Lake_joinRelative(v_dir_934_, v___x_1341_);
v___x_1435_ = l_System_FilePath_pathExists(v_configFile_1342_);
v___x_1468_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1469_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1469_ == 0)
{
goto v___jp_1436_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1471_ == 0)
{
if (v___x_1469_ == 0)
{
goto v___jp_1436_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = ((size_t)0ULL);
v___x_1473_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1468_, v___x_1472_, v___x_1473_, v___x_1470_, v_a_940_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_dec_ref(v___x_1474_);
goto v___jp_1436_;
}
else
{
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1474_;
}
}
}
else
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1468_, v___x_1475_, v___x_1476_, v___x_1470_, v_a_940_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec_ref(v___x_1477_);
goto v___jp_1436_;
}
else
{
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1477_;
}
}
}
v___jp_942_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_box(0);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
v___jp_946_:
{
if (v_offline_939_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_948_ = lean_box(0);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_box(0);
v___x_951_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_934_);
v___x_952_ = l_Lake_joinRelative(v_dir_934_, v___x_951_);
lean_inc_ref(v___x_952_);
v___x_953_ = l_Lake_joinRelative(v___x_952_, v___x_945_);
v___x_954_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_955_ = lean_box(1);
v___x_956_ = l_Lean_Options_empty;
v___x_957_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_958_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v___x_958_, 0, v_env_938_);
lean_ctor_set(v___x_958_, 1, v___x_948_);
lean_ctor_set(v___x_958_, 2, v_dir_934_);
lean_ctor_set(v___x_958_, 3, v___x_949_);
lean_ctor_set(v___x_958_, 4, v___x_950_);
lean_ctor_set(v___x_958_, 5, v___x_951_);
lean_ctor_set(v___x_958_, 6, v___x_952_);
lean_ctor_set(v___x_958_, 7, v___x_945_);
lean_ctor_set(v___x_958_, 8, v___x_953_);
lean_ctor_set(v___x_958_, 9, v___x_954_);
lean_ctor_set(v___x_958_, 10, v___x_955_);
lean_ctor_set(v___x_958_, 11, v___x_956_);
lean_ctor_set(v___x_958_, 12, v___x_957_);
lean_ctor_set(v___x_958_, 13, v___x_957_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*14, v_offline_939_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*14 + 1, v_offline_939_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*14 + 2, v_offline_939_);
v___x_959_ = l_Lean_NameSet_empty;
v___x_960_ = l_Lake_updateManifest(v___x_958_, v___x_959_, v___y_947_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec_ref(v___y_947_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
v___jp_963_:
{
if (lean_obj_tag(v___y_964_) == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_965_);
v___x_967_ = lean_apply_2(v___y_965_, v___x_966_, lean_box(0));
v___y_947_ = v___y_965_;
goto v___jp_946_;
}
else
{
lean_dec_ref(v___y_964_);
v___y_947_ = v___y_965_;
goto v___jp_946_;
}
}
v___jp_968_:
{
switch(v_tmp_936_)
{
case 3:
{
v___y_964_ = v___y_969_;
v___y_965_ = v___y_970_;
goto v___jp_963_;
}
case 4:
{
v___y_964_ = v___y_969_;
v___y_965_ = v___y_970_;
goto v___jp_963_;
}
default: 
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
v___jp_973_:
{
if (v_a_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_975_);
v___x_978_ = lean_apply_2(v___y_975_, v___x_977_, lean_box(0));
v___y_969_ = v___y_974_;
v___y_970_ = v___y_975_;
goto v___jp_968_;
}
else
{
v___y_969_ = v___y_974_;
v___y_970_ = v___y_975_;
goto v___jp_968_;
}
}
v___jp_979_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v___x_984_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_934_);
v___x_985_ = l_Lake_joinRelative(v_dir_934_, v___x_984_);
v___x_986_ = 4;
v___x_987_ = lean_io_prim_handle_mk(v___x_985_, v___x_986_);
lean_dec_ref(v___x_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_990_ = lean_io_prim_handle_put_str(v_a_988_, v___x_989_);
lean_dec(v_a_988_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
lean_dec_ref(v___x_990_);
v___x_991_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_934_);
v___x_992_ = l_Lake_joinRelative(v_dir_934_, v___x_991_);
v___x_993_ = lean_string_utf8_byte_size(v___y_982_);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_nat_dec_eq(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v___y_980_);
v___x_996_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_997_ = lean_string_append(v___y_982_, v___x_996_);
v___x_998_ = l_IO_FS_writeFile(v___x_992_, v___x_997_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_992_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_dec_ref(v___x_998_);
v___y_969_ = v___y_981_;
v___y_970_ = v___y_983_;
goto v___jp_968_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v___y_981_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1003_ = lean_io_error_to_string(v_a_999_);
v___x_1004_ = 3;
v___x_1005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_1004_);
v___x_1006_ = lean_apply_2(v___y_983_, v___x_1005_, lean_box(0));
v___x_1007_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1007_);
v___x_1009_ = v___x_1001_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_githash_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_dec_ref(v___y_982_);
v_githash_1012_ = lean_ctor_get(v___y_980_, 1);
lean_inc_ref(v_githash_1012_);
lean_dec_ref(v___y_980_);
v___x_1013_ = lean_string_utf8_byte_size(v_githash_1012_);
lean_dec_ref(v_githash_1012_);
v___x_1014_ = lean_nat_dec_eq(v___x_1013_, v___x_994_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1015_ = l_System_FilePath_pathExists(v___x_992_);
lean_dec_ref(v___x_992_);
v___x_1016_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1017_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1017_ == 0)
{
v___y_974_ = v___y_981_;
v___y_975_ = v___y_983_;
v_a_976_ = v___x_1015_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1019_ == 0)
{
if (v___x_1017_ == 0)
{
v___y_974_ = v___y_981_;
v___y_975_ = v___y_983_;
v_a_976_ = v___x_1015_;
goto v___jp_973_;
}
else
{
size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_983_);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1016_, v___x_1020_, v___x_1021_, v___x_1018_, v___y_983_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref(v___x_1022_);
v___y_974_ = v___y_981_;
v___y_975_ = v___y_983_;
v_a_976_ = v___x_1015_;
goto v___jp_973_;
}
else
{
lean_dec_ref(v___y_983_);
lean_dec(v___y_981_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
return v___x_1022_;
}
}
}
else
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_983_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1016_, v___x_1023_, v___x_1024_, v___x_1018_, v___y_983_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref(v___x_1025_);
v___y_974_ = v___y_981_;
v___y_975_ = v___y_983_;
v_a_976_ = v___x_1015_;
goto v___jp_973_;
}
else
{
lean_dec_ref(v___y_983_);
lean_dec(v___y_981_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
return v___x_1025_;
}
}
}
}
else
{
lean_dec_ref(v___x_992_);
v___y_969_ = v___y_981_;
v___y_970_ = v___y_983_;
goto v___jp_968_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v_a_1026_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1028_ = v___x_990_;
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_990_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1030_ = lean_io_error_to_string(v_a_1026_);
v___x_1031_ = 3;
v___x_1032_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_1031_);
v___x_1033_ = lean_apply_2(v___y_983_, v___x_1032_, lean_box(0));
v___x_1034_ = lean_box(0);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1034_);
v___x_1036_ = v___x_1028_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
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
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v_a_1039_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1041_ = v___x_987_;
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_987_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1043_ = lean_io_error_to_string(v_a_1039_);
v___x_1044_ = 3;
v___x_1045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*1, v___x_1044_);
v___x_1046_ = lean_apply_2(v___y_983_, v___x_1045_, lean_box(0));
v___x_1047_ = lean_box(0);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1047_);
v___x_1049_ = v___x_1041_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
v___jp_1052_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1056_);
v___x_1058_ = lean_apply_2(v___y_1056_, v___x_1057_, lean_box(0));
v___y_980_ = v___y_1053_;
v___y_981_ = v___y_1054_;
v___y_982_ = v___y_1055_;
v___y_983_ = v___y_1056_;
goto v___jp_979_;
}
v___jp_1059_:
{
if (lean_obj_tag(v___y_1064_) == 0)
{
lean_dec_ref(v___y_1064_);
v___y_980_ = v___y_1060_;
v___y_981_ = v___y_1061_;
v___y_982_ = v___y_1062_;
v___y_983_ = v___y_1063_;
goto v___jp_979_;
}
else
{
lean_dec_ref(v___y_1064_);
v___y_1053_ = v___y_1060_;
v___y_1054_ = v___y_1061_;
v___y_1055_ = v___y_1062_;
v___y_1056_ = v___y_1063_;
goto v___jp_1052_;
}
}
v___jp_1065_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = l_Lake_Git_upstreamBranch;
v___x_1071_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_934_);
v___x_1074_ = l_Lake_GitRepo_checkoutBranch(v___x_1070_, v_dir_934_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = lean_array_get_size(v_a_1075_);
v___x_1077_ = lean_nat_dec_lt(v___x_1072_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec(v_a_1075_);
v___y_980_ = v___y_1066_;
v___y_981_ = v___y_1067_;
v___y_982_ = v___y_1068_;
v___y_983_ = v___y_1069_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_nat_dec_le(v___x_1076_, v___x_1076_);
if (v___x_1079_ == 0)
{
if (v___x_1077_ == 0)
{
lean_dec(v_a_1075_);
v___y_980_ = v___y_1066_;
v___y_981_ = v___y_1067_;
v___y_982_ = v___y_1068_;
v___y_983_ = v___y_1069_;
goto v___jp_979_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = lean_usize_of_nat(v___x_1076_);
lean_inc_ref(v___y_1069_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1075_, v___x_1080_, v___x_1081_, v___x_1078_, v___y_1069_);
lean_dec(v_a_1075_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec_ref(v___x_1082_);
v___y_980_ = v___y_1066_;
v___y_981_ = v___y_1067_;
v___y_982_ = v___y_1068_;
v___y_983_ = v___y_1069_;
goto v___jp_979_;
}
else
{
v___y_1060_ = v___y_1066_;
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___y_1069_;
v___y_1064_ = v___x_1082_;
goto v___jp_1059_;
}
}
}
else
{
size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = lean_usize_of_nat(v___x_1076_);
lean_inc_ref(v___y_1069_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1075_, v___x_1083_, v___x_1084_, v___x_1078_, v___y_1069_);
lean_dec(v_a_1075_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_dec_ref(v___x_1085_);
v___y_980_ = v___y_1066_;
v___y_981_ = v___y_1067_;
v___y_982_ = v___y_1068_;
v___y_983_ = v___y_1069_;
goto v___jp_979_;
}
else
{
v___y_1060_ = v___y_1066_;
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___y_1069_;
v___y_1064_ = v___x_1085_;
goto v___jp_1059_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1074_);
v___x_1087_ = lean_array_get_size(v_a_1086_);
v___x_1088_ = lean_nat_dec_lt(v___x_1072_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec(v_a_1086_);
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1069_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_nat_dec_le(v___x_1087_, v___x_1087_);
if (v___x_1090_ == 0)
{
if (v___x_1088_ == 0)
{
lean_dec(v_a_1086_);
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1069_;
goto v___jp_1052_;
}
else
{
size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = lean_usize_of_nat(v___x_1087_);
lean_inc_ref(v___y_1069_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1086_, v___x_1091_, v___x_1092_, v___x_1089_, v___y_1069_);
lean_dec(v_a_1086_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_dec_ref(v___x_1093_);
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1069_;
goto v___jp_1052_;
}
else
{
v___y_1060_ = v___y_1066_;
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___y_1069_;
v___y_1064_ = v___x_1093_;
goto v___jp_1059_;
}
}
}
else
{
size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((size_t)0ULL);
v___x_1095_ = lean_usize_of_nat(v___x_1087_);
lean_inc_ref(v___y_1069_);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1086_, v___x_1094_, v___x_1095_, v___x_1089_, v___y_1069_);
lean_dec(v_a_1086_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref(v___x_1096_);
v___y_1053_ = v___y_1066_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1069_;
goto v___jp_1052_;
}
else
{
v___y_1060_ = v___y_1066_;
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___y_1069_;
v___y_1064_ = v___x_1096_;
goto v___jp_1059_;
}
}
}
}
}
else
{
v___y_980_ = v___y_1066_;
v___y_981_ = v___y_1067_;
v___y_982_ = v___y_1068_;
v___y_983_ = v___y_1069_;
goto v___jp_979_;
}
}
v___jp_1097_:
{
if (lean_obj_tag(v___y_1102_) == 0)
{
lean_dec_ref(v___y_1102_);
v___y_1066_ = v___y_1098_;
v___y_1067_ = v___y_1099_;
v___y_1068_ = v___y_1100_;
v___y_1069_ = v___y_1101_;
goto v___jp_1065_;
}
else
{
lean_dec_ref(v___y_1102_);
v___y_1053_ = v___y_1098_;
v___y_1054_ = v___y_1099_;
v___y_1055_ = v___y_1100_;
v___y_1056_ = v___y_1101_;
goto v___jp_1052_;
}
}
v___jp_1103_:
{
if (v_a_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_934_);
v___x_1111_ = l_Lake_GitRepo_quietInit(v_dir_934_, v___x_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_a_1112_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = lean_array_get_size(v_a_1112_);
v___x_1114_ = lean_nat_dec_lt(v___x_1109_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec(v_a_1112_);
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v___y_1106_;
v___y_1069_ = v___y_1107_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_nat_dec_le(v___x_1113_, v___x_1113_);
if (v___x_1116_ == 0)
{
if (v___x_1114_ == 0)
{
lean_dec(v_a_1112_);
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v___y_1106_;
v___y_1069_ = v___y_1107_;
goto v___jp_1065_;
}
else
{
size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = lean_usize_of_nat(v___x_1113_);
lean_inc_ref(v___y_1107_);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1112_, v___x_1117_, v___x_1118_, v___x_1115_, v___y_1107_);
lean_dec(v_a_1112_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref(v___x_1119_);
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v___y_1106_;
v___y_1069_ = v___y_1107_;
goto v___jp_1065_;
}
else
{
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v___y_1106_;
v___y_1101_ = v___y_1107_;
v___y_1102_ = v___x_1119_;
goto v___jp_1097_;
}
}
}
else
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1113_);
lean_inc_ref(v___y_1107_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1112_, v___x_1120_, v___x_1121_, v___x_1115_, v___y_1107_);
lean_dec(v_a_1112_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_dec_ref(v___x_1122_);
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v___y_1106_;
v___y_1069_ = v___y_1107_;
goto v___jp_1065_;
}
else
{
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v___y_1106_;
v___y_1101_ = v___y_1107_;
v___y_1102_ = v___x_1122_;
goto v___jp_1097_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1111_);
v___x_1124_ = lean_array_get_size(v_a_1123_);
v___x_1125_ = lean_nat_dec_lt(v___x_1109_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_dec(v_a_1123_);
v___y_1053_ = v___y_1104_;
v___y_1054_ = v___y_1105_;
v___y_1055_ = v___y_1106_;
v___y_1056_ = v___y_1107_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
if (v___x_1127_ == 0)
{
if (v___x_1125_ == 0)
{
lean_dec(v_a_1123_);
v___y_1053_ = v___y_1104_;
v___y_1054_ = v___y_1105_;
v___y_1055_ = v___y_1106_;
v___y_1056_ = v___y_1107_;
goto v___jp_1052_;
}
else
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1124_);
lean_inc_ref(v___y_1107_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1123_, v___x_1128_, v___x_1129_, v___x_1126_, v___y_1107_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec_ref(v___x_1130_);
v___y_1053_ = v___y_1104_;
v___y_1054_ = v___y_1105_;
v___y_1055_ = v___y_1106_;
v___y_1056_ = v___y_1107_;
goto v___jp_1052_;
}
else
{
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v___y_1106_;
v___y_1101_ = v___y_1107_;
v___y_1102_ = v___x_1130_;
goto v___jp_1097_;
}
}
}
else
{
size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = lean_usize_of_nat(v___x_1124_);
lean_inc_ref(v___y_1107_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1123_, v___x_1131_, v___x_1132_, v___x_1126_, v___y_1107_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref(v___x_1133_);
v___y_1053_ = v___y_1104_;
v___y_1054_ = v___y_1105_;
v___y_1055_ = v___y_1106_;
v___y_1056_ = v___y_1107_;
goto v___jp_1052_;
}
else
{
v___y_1098_ = v___y_1104_;
v___y_1099_ = v___y_1105_;
v___y_1100_ = v___y_1106_;
v___y_1101_ = v___y_1107_;
v___y_1102_ = v___x_1133_;
goto v___jp_1097_;
}
}
}
}
}
else
{
v___y_980_ = v___y_1104_;
v___y_981_ = v___y_1105_;
v___y_982_ = v___y_1106_;
v___y_983_ = v___y_1107_;
goto v___jp_979_;
}
}
v___jp_1134_:
{
uint8_t v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
lean_inc_ref(v_dir_934_);
v___x_1139_ = l_Lake_GitRepo_insideWorkTree(v_dir_934_);
v___x_1140_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1141_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1141_ == 0)
{
v___y_1104_ = v___y_1135_;
v___y_1105_ = v___y_1136_;
v___y_1106_ = v___y_1137_;
v___y_1107_ = v___y_1138_;
v_a_1108_ = v___x_1139_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1143_ == 0)
{
if (v___x_1141_ == 0)
{
v___y_1104_ = v___y_1135_;
v___y_1105_ = v___y_1136_;
v___y_1106_ = v___y_1137_;
v___y_1107_ = v___y_1138_;
v_a_1108_ = v___x_1139_;
goto v___jp_1103_;
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1138_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1140_, v___x_1144_, v___x_1145_, v___x_1142_, v___y_1138_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_dec_ref(v___x_1146_);
v___y_1104_ = v___y_1135_;
v___y_1105_ = v___y_1136_;
v___y_1106_ = v___y_1137_;
v___y_1107_ = v___y_1138_;
v_a_1108_ = v___x_1139_;
goto v___jp_1103_;
}
else
{
lean_dec_ref(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
return v___x_1146_;
}
}
}
else
{
size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1138_);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1140_, v___x_1147_, v___x_1148_, v___x_1142_, v___y_1138_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_dec_ref(v___x_1149_);
v___y_1104_ = v___y_1135_;
v___y_1105_ = v___y_1136_;
v___y_1106_ = v___y_1137_;
v___y_1107_ = v___y_1138_;
v_a_1108_ = v___x_1139_;
goto v___jp_1103_;
}
else
{
lean_dec_ref(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
return v___x_1149_;
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_IO_FS_writeFile(v___y_1155_, v___y_1156_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v___y_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref(v___x_1157_);
v___y_1135_ = v___y_1151_;
v___y_1136_ = v___y_1152_;
v___y_1137_ = v___y_1153_;
v___y_1138_ = v___y_1154_;
goto v___jp_1134_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec_ref(v_env_938_);
lean_dec_ref(v_dir_934_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1162_ = lean_io_error_to_string(v_a_1158_);
v___x_1163_ = 3;
v___x_1164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*1, v___x_1163_);
v___x_1165_ = lean_apply_2(v___y_1154_, v___x_1164_, lean_box(0));
v___x_1166_ = lean_box(0);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1166_);
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
v___jp_1171_:
{
if (v_a_1177_ == 0)
{
uint8_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 4;
v___x_1179_ = l_Lake_instDecidableEqInitTemplate(v_tmp_936_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_935_);
v___x_1181_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1180_);
lean_dec_ref(v___x_1180_);
v___y_1151_ = v___y_1172_;
v___y_1152_ = v___y_1173_;
v___y_1153_ = v___y_1174_;
v___y_1154_ = v___y_1176_;
v___y_1155_ = v___y_1175_;
v___y_1156_ = v___x_1181_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_935_);
v___x_1183_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1182_);
lean_dec_ref(v___x_1182_);
v___y_1151_ = v___y_1172_;
v___y_1152_ = v___y_1173_;
v___y_1153_ = v___y_1174_;
v___y_1154_ = v___y_1176_;
v___y_1155_ = v___y_1175_;
v___y_1156_ = v___x_1183_;
goto v___jp_1150_;
}
}
else
{
lean_dec_ref(v___y_1175_);
lean_dec(v_name_935_);
v___y_1135_ = v___y_1172_;
v___y_1136_ = v___y_1173_;
v___y_1137_ = v___y_1174_;
v___y_1138_ = v___y_1176_;
goto v___jp_1134_;
}
}
v___jp_1184_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1189_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_934_);
v___x_1190_ = l_Lake_joinRelative(v_dir_934_, v___x_1189_);
v___x_1191_ = l_System_FilePath_pathExists(v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1193_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1193_ == 0)
{
v___y_1172_ = v___y_1185_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___x_1190_;
v___y_1176_ = v___y_1188_;
v_a_1177_ = v___x_1191_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1195_ == 0)
{
if (v___x_1193_ == 0)
{
v___y_1172_ = v___y_1185_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___x_1190_;
v___y_1176_ = v___y_1188_;
v_a_1177_ = v___x_1191_;
goto v___jp_1171_;
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1188_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1192_, v___x_1196_, v___x_1197_, v___x_1194_, v___y_1188_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_dec_ref(v___x_1198_);
v___y_1172_ = v___y_1185_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___x_1190_;
v___y_1176_ = v___y_1188_;
v_a_1177_ = v___x_1191_;
goto v___jp_1171_;
}
else
{
lean_dec_ref(v___x_1190_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1198_;
}
}
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1188_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1192_, v___x_1199_, v___x_1200_, v___x_1194_, v___y_1188_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_dec_ref(v___x_1201_);
v___y_1172_ = v___y_1185_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1187_;
v___y_1175_ = v___x_1190_;
v___y_1176_ = v___y_1188_;
v_a_1177_ = v___x_1191_;
goto v___jp_1171_;
}
else
{
lean_dec_ref(v___x_1190_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1201_;
}
}
}
}
v___jp_1202_:
{
if (v_a_1209_ == 0)
{
uint8_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 1;
v___x_1211_ = l_Lake_instDecidableEqInitTemplate(v_tmp_936_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1208_);
v___x_1213_ = l_IO_FS_writeFile(v___y_1205_, v___x_1212_);
lean_dec_ref(v___x_1212_);
lean_dec_ref(v___y_1205_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_dec_ref(v___x_1213_);
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1204_;
v___y_1187_ = v___y_1207_;
v___y_1188_ = v___y_1206_;
goto v___jp_1184_;
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1218_ = lean_io_error_to_string(v_a_1214_);
v___x_1219_ = 3;
v___x_1220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*1, v___x_1219_);
v___x_1221_ = lean_apply_2(v___y_1206_, v___x_1220_, lean_box(0));
v___x_1222_ = lean_box(0);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1222_);
v___x_1224_ = v___x_1216_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec(v___y_1208_);
v___x_1227_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1228_ = l_IO_FS_writeFile(v___y_1205_, v___x_1227_);
lean_dec_ref(v___y_1205_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref(v___x_1228_);
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1204_;
v___y_1187_ = v___y_1207_;
v___y_1188_ = v___y_1206_;
goto v___jp_1184_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1241_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1241_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1233_ = lean_io_error_to_string(v_a_1229_);
v___x_1234_ = 3;
v___x_1235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*1, v___x_1234_);
v___x_1236_ = lean_apply_2(v___y_1206_, v___x_1235_, lean_box(0));
v___x_1237_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1237_);
v___x_1239_ = v___x_1231_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1205_);
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1204_;
v___y_1187_ = v___y_1207_;
v___y_1188_ = v___y_1206_;
goto v___jp_1184_;
}
}
v___jp_1242_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1248_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_934_);
v___x_1249_ = l_Lake_joinRelative(v_dir_934_, v___x_1248_);
v___x_1250_ = l_System_FilePath_pathExists(v___x_1249_);
v___x_1251_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1252_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1252_ == 0)
{
v___y_1203_ = v___y_1243_;
v___y_1204_ = v___y_1244_;
v___y_1205_ = v___x_1249_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1246_;
v___y_1208_ = v___y_1247_;
v_a_1209_ = v___x_1250_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1254_ == 0)
{
if (v___x_1252_ == 0)
{
v___y_1203_ = v___y_1243_;
v___y_1204_ = v___y_1244_;
v___y_1205_ = v___x_1249_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1246_;
v___y_1208_ = v___y_1247_;
v_a_1209_ = v___x_1250_;
goto v___jp_1202_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1245_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1251_, v___x_1255_, v___x_1256_, v___x_1253_, v___y_1245_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_dec_ref(v___x_1257_);
v___y_1203_ = v___y_1243_;
v___y_1204_ = v___y_1244_;
v___y_1205_ = v___x_1249_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1246_;
v___y_1208_ = v___y_1247_;
v_a_1209_ = v___x_1250_;
goto v___jp_1202_;
}
else
{
lean_dec_ref(v___x_1249_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1257_;
}
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1245_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1251_, v___x_1258_, v___x_1259_, v___x_1253_, v___y_1245_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_dec_ref(v___x_1260_);
v___y_1203_ = v___y_1243_;
v___y_1204_ = v___y_1244_;
v___y_1205_ = v___x_1249_;
v___y_1206_ = v___y_1245_;
v___y_1207_ = v___y_1246_;
v___y_1208_ = v___y_1247_;
v_a_1209_ = v___x_1250_;
goto v___jp_1202_;
}
else
{
lean_dec_ref(v___x_1249_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1260_;
}
}
}
}
v___jp_1261_:
{
switch(v_tmp_936_)
{
case 0:
{
v___y_1243_ = v___y_1262_;
v___y_1244_ = v___y_1263_;
v___y_1245_ = v___y_1266_;
v___y_1246_ = v___y_1264_;
v___y_1247_ = v___y_1265_;
goto v___jp_1242_;
}
case 1:
{
v___y_1243_ = v___y_1262_;
v___y_1244_ = v___y_1263_;
v___y_1245_ = v___y_1266_;
v___y_1246_ = v___y_1264_;
v___y_1247_ = v___y_1265_;
goto v___jp_1242_;
}
default: 
{
lean_dec(v___y_1265_);
v___y_1185_ = v___y_1262_;
v___y_1186_ = v___y_1263_;
v___y_1187_ = v___y_1264_;
v___y_1188_ = v___y_1266_;
goto v___jp_1184_;
}
}
}
v___jp_1267_:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_IO_FS_writeFile(v___y_1273_, v___y_1274_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v___x_1275_);
v___y_1262_ = v___y_1268_;
v___y_1263_ = v___y_1270_;
v___y_1264_ = v___y_1271_;
v___y_1265_ = v___y_1272_;
v___y_1266_ = v___y_1269_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1280_ = lean_io_error_to_string(v_a_1276_);
v___x_1281_ = 3;
v___x_1282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*1, v___x_1281_);
v___x_1283_ = lean_apply_2(v___y_1269_, v___x_1282_, lean_box(0));
v___x_1284_ = lean_box(0);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1286_ = v___x_1278_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
v___jp_1289_:
{
uint8_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = 4;
v___x_1297_ = l_Lake_instDecidableEqInitTemplate(v_tmp_936_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = 1;
lean_inc(v___y_1294_);
v___x_1299_ = l_Lean_Name_toString(v___y_1294_, v___x_1298_);
lean_inc(v___y_1294_);
v___x_1300_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1299_, v___y_1294_);
lean_dec_ref(v___x_1299_);
v___y_1268_ = v___y_1290_;
v___y_1269_ = v___y_1295_;
v___y_1270_ = v___y_1291_;
v___y_1271_ = v___y_1292_;
v___y_1272_ = v___y_1294_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v___x_1300_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1301_; 
lean_inc(v___y_1294_);
v___x_1301_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1294_);
v___y_1268_ = v___y_1290_;
v___y_1269_ = v___y_1295_;
v___y_1270_ = v___y_1291_;
v___y_1271_ = v___y_1292_;
v___y_1272_ = v___y_1294_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v___x_1301_;
goto v___jp_1267_;
}
}
v___jp_1302_:
{
if (v_a_1310_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = l_IO_FS_createDirAll(v___y_1304_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1311_);
v___x_1312_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1313_ = l_IO_FS_writeFile(v___y_1309_, v___x_1312_);
lean_dec_ref(v___y_1309_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref(v___x_1313_);
v___y_1290_ = v___y_1303_;
v___y_1291_ = v___y_1305_;
v___y_1292_ = v___y_1306_;
v___y_1293_ = v___y_1308_;
v___y_1294_ = v___y_1307_;
v___y_1295_ = v_a_940_;
goto v___jp_1289_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1326_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
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
v___x_1321_ = lean_apply_2(v_a_940_, v___x_1320_, lean_box(0));
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
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1327_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1329_ = v___x_1311_;
v_isShared_1330_ = v_isSharedCheck_1339_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1311_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1339_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1331_ = lean_io_error_to_string(v_a_1327_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = lean_apply_2(v_a_940_, v___x_1333_, lean_box(0));
v___x_1335_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1335_);
v___x_1337_ = v___x_1329_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_dec_ref(v___y_1309_);
lean_dec_ref(v___y_1304_);
v___y_1290_ = v___y_1303_;
v___y_1291_ = v___y_1305_;
v___y_1292_ = v___y_1306_;
v___y_1293_ = v___y_1308_;
v___y_1294_ = v___y_1307_;
v___y_1295_ = v_a_940_;
goto v___jp_1289_;
}
}
v___jp_1343_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_inc(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc(v_name_935_);
v___x_1349_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_936_, v_lang_937_, v_name_935_, v___y_1347_, v___y_1348_);
v___x_1350_ = l_IO_FS_writeFile(v_configFile_1342_, v___x_1349_);
lean_dec_ref(v___x_1349_);
lean_dec_ref(v_configFile_1342_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_dec_ref(v___x_1350_);
if (lean_obj_tag(v___y_1345_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_val_1351_ = lean_ctor_get(v___y_1345_, 0);
lean_inc(v_val_1351_);
lean_dec_ref(v___y_1345_);
v___x_1352_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(v_val_1351_);
v___x_1353_ = l_System_FilePath_withExtension(v_val_1351_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_1353_);
v___x_1355_ = l_Lake_joinRelative(v___x_1353_, v___x_1354_);
v___x_1356_ = l_System_FilePath_pathExists(v___x_1355_);
v___x_1357_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1358_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1358_ == 0)
{
v___y_1303_ = v___y_1344_;
v___y_1304_ = v___x_1353_;
v___y_1305_ = v___y_1348_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v_val_1351_;
v___y_1309_ = v___x_1355_;
v_a_1310_ = v___x_1356_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1360_ == 0)
{
if (v___x_1358_ == 0)
{
v___y_1303_ = v___y_1344_;
v___y_1304_ = v___x_1353_;
v___y_1305_ = v___y_1348_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v_val_1351_;
v___y_1309_ = v___x_1355_;
v_a_1310_ = v___x_1356_;
goto v___jp_1302_;
}
else
{
size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1357_, v___x_1361_, v___x_1362_, v___x_1359_, v_a_940_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_dec_ref(v___x_1363_);
v___y_1303_ = v___y_1344_;
v___y_1304_ = v___x_1353_;
v___y_1305_ = v___y_1348_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v_val_1351_;
v___y_1309_ = v___x_1355_;
v_a_1310_ = v___x_1356_;
goto v___jp_1302_;
}
else
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1353_);
lean_dec(v_val_1351_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1363_;
}
}
}
else
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1357_, v___x_1364_, v___x_1365_, v___x_1359_, v_a_940_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_dec_ref(v___x_1366_);
v___y_1303_ = v___y_1344_;
v___y_1304_ = v___x_1353_;
v___y_1305_ = v___y_1348_;
v___y_1306_ = v___y_1346_;
v___y_1307_ = v___y_1347_;
v___y_1308_ = v_val_1351_;
v___y_1309_ = v___x_1355_;
v_a_1310_ = v___x_1356_;
goto v___jp_1302_;
}
else
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1353_);
lean_dec(v_val_1351_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1366_;
}
}
}
}
else
{
lean_dec(v___y_1345_);
v___y_1262_ = v___y_1344_;
v___y_1263_ = v___y_1348_;
v___y_1264_ = v___y_1346_;
v___y_1265_ = v___y_1347_;
v___y_1266_ = v_a_940_;
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v_a_1367_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1369_ = v___x_1350_;
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1350_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1371_ = lean_io_error_to_string(v_a_1367_);
v___x_1372_ = 3;
v___x_1373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*1, v___x_1372_);
v___x_1374_ = lean_apply_2(v_a_940_, v___x_1373_, lean_box(0));
v___x_1375_ = lean_box(0);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1375_);
v___x_1377_ = v___x_1369_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
v___jp_1380_:
{
lean_object* v_lean_1383_; lean_object* v_toolchain_1384_; lean_object* v___x_1385_; 
v_lean_1383_ = lean_ctor_get(v_env_938_, 1);
v_toolchain_1384_ = lean_ctor_get(v_env_938_, 18);
lean_inc_ref(v_toolchain_1384_);
v___x_1385_ = l_Lake_ToolchainVer_ofString(v_toolchain_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_ver_1386_; lean_object* v___x_1387_; 
v_ver_1386_ = lean_ctor_get(v___x_1385_, 1);
lean_inc_ref(v_ver_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_ver_1386_);
lean_inc_ref(v_toolchain_1384_);
lean_inc_ref(v_lean_1383_);
v___y_1344_ = v_lean_1383_;
v___y_1345_ = v_snd_1382_;
v___y_1346_ = v_toolchain_1384_;
v___y_1347_ = v_fst_1381_;
v___y_1348_ = v___x_1387_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1388_; 
lean_dec_ref(v___x_1385_);
v___x_1388_ = lean_box(0);
lean_inc_ref(v_toolchain_1384_);
lean_inc_ref(v_lean_1383_);
v___y_1344_ = v_lean_1383_;
v___y_1345_ = v_snd_1382_;
v___y_1346_ = v_toolchain_1384_;
v___y_1347_ = v_fst_1381_;
v___y_1348_ = v___x_1388_;
goto v___jp_1343_;
}
}
v___jp_1389_:
{
if (v_a_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1390_);
v_fst_1381_ = v___y_1391_;
v_snd_1382_ = v___x_1393_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1394_; 
lean_dec_ref(v___y_1390_);
v___x_1394_ = lean_box(0);
v_fst_1381_ = v___y_1391_;
v_snd_1382_ = v___x_1394_;
goto v___jp_1380_;
}
}
v___jp_1395_:
{
if (v___y_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
lean_dec_ref(v___y_1396_);
lean_inc(v_name_935_);
v___x_1399_ = l_Lake_toUpperCamelCase(v_name_935_);
lean_inc(v___x_1399_);
v___x_1400_ = l_Lean_modToFilePath(v_dir_934_, v___x_1399_, v___y_1397_);
lean_dec_ref(v___y_1397_);
v___x_1401_ = l_System_FilePath_pathExists(v___x_1400_);
v___x_1402_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1403_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1403_ == 0)
{
v___y_1390_ = v___x_1400_;
v___y_1391_ = v___x_1399_;
v_a_1392_ = v___x_1401_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1405_ == 0)
{
if (v___x_1403_ == 0)
{
v___y_1390_ = v___x_1400_;
v___y_1391_ = v___x_1399_;
v_a_1392_ = v___x_1401_;
goto v___jp_1389_;
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1402_, v___x_1406_, v___x_1407_, v___x_1404_, v_a_940_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_dec_ref(v___x_1408_);
v___y_1390_ = v___x_1400_;
v___y_1391_ = v___x_1399_;
v_a_1392_ = v___x_1401_;
goto v___jp_1389_;
}
else
{
lean_dec_ref(v___x_1400_);
lean_dec(v___x_1399_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1408_;
}
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1402_, v___x_1409_, v___x_1410_, v___x_1404_, v_a_940_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref(v___x_1411_);
v___y_1390_ = v___x_1400_;
v___y_1391_ = v___x_1399_;
v_a_1392_ = v___x_1401_;
goto v___jp_1389_;
}
else
{
lean_dec_ref(v___x_1400_);
lean_dec(v___x_1399_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1411_;
}
}
}
}
else
{
lean_object* v___x_1412_; 
lean_dec_ref(v___y_1397_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___y_1396_);
lean_inc(v_name_935_);
v_fst_1381_ = v_name_935_;
v_snd_1382_ = v___x_1412_;
goto v___jp_1380_;
}
}
v___jp_1413_:
{
uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = 1;
v___x_1418_ = l_Lake_instDecidableEqInitTemplate(v_tmp_936_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___y_1414_;
v___y_1398_ = v_a_1416_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___y_1415_;
v___y_1397_ = v___y_1414_;
v___y_1398_ = v___x_1418_;
goto v___jp_1395_;
}
}
v___jp_1419_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1420_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_935_);
v___x_1421_ = l_Lean_modToFilePath(v_dir_934_, v_name_935_, v___x_1420_);
v___x_1422_ = l_System_FilePath_pathExists(v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1424_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1424_ == 0)
{
v___y_1414_ = v___x_1420_;
v___y_1415_ = v___x_1421_;
v_a_1416_ = v___x_1422_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1426_ == 0)
{
if (v___x_1424_ == 0)
{
v___y_1414_ = v___x_1420_;
v___y_1415_ = v___x_1421_;
v_a_1416_ = v___x_1422_;
goto v___jp_1413_;
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1423_, v___x_1427_, v___x_1428_, v___x_1425_, v_a_940_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref(v___x_1429_);
v___y_1414_ = v___x_1420_;
v___y_1415_ = v___x_1421_;
v_a_1416_ = v___x_1422_;
goto v___jp_1413_;
}
else
{
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1429_;
}
}
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_940_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1423_, v___x_1430_, v___x_1431_, v___x_1425_, v_a_940_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref(v___x_1432_);
v___y_1414_ = v___x_1420_;
v___y_1415_ = v___x_1421_;
v_a_1416_ = v___x_1422_;
goto v___jp_1413_;
}
else
{
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___x_1432_;
}
}
}
}
v___jp_1433_:
{
if (lean_obj_tag(v___y_1434_) == 0)
{
lean_dec_ref(v___y_1434_);
goto v___jp_1419_;
}
else
{
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
return v___y_1434_;
}
}
v___jp_1436_:
{
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_934_);
v___x_1439_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_934_, v_tmp_936_, v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = lean_array_get_size(v_a_1440_);
v___x_1442_ = lean_nat_dec_lt(v___x_1437_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_dec(v_a_1440_);
goto v___jp_1419_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_nat_dec_le(v___x_1441_, v___x_1441_);
if (v___x_1444_ == 0)
{
if (v___x_1442_ == 0)
{
lean_dec(v_a_1440_);
goto v___jp_1419_;
}
else
{
size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1441_);
lean_inc_ref(v_a_940_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1440_, v___x_1445_, v___x_1446_, v___x_1443_, v_a_940_);
lean_dec(v_a_1440_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_dec_ref(v___x_1447_);
goto v___jp_1419_;
}
else
{
v___y_1434_ = v___x_1447_;
goto v___jp_1433_;
}
}
}
else
{
size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = lean_usize_of_nat(v___x_1441_);
lean_inc_ref(v_a_940_);
v___x_1450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1440_, v___x_1448_, v___x_1449_, v___x_1443_, v_a_940_);
lean_dec(v_a_1440_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref(v___x_1450_);
goto v___jp_1419_;
}
else
{
v___y_1434_ = v___x_1450_;
goto v___jp_1433_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1439_);
v___x_1452_ = lean_array_get_size(v_a_1451_);
v___x_1453_ = lean_nat_dec_lt(v___x_1437_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v_a_1451_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_nat_dec_le(v___x_1452_, v___x_1452_);
if (v___x_1457_ == 0)
{
if (v___x_1453_ == 0)
{
lean_dec(v_a_1451_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
goto v___jp_942_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1452_);
lean_inc_ref(v_a_940_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1451_, v___x_1458_, v___x_1459_, v___x_1456_, v_a_940_);
lean_dec(v_a_1451_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref(v___x_1460_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
goto v___jp_942_;
}
else
{
v___y_1434_ = v___x_1460_;
goto v___jp_1433_;
}
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1452_);
lean_inc_ref(v_a_940_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1451_, v___x_1461_, v___x_1462_, v___x_1456_, v_a_940_);
lean_dec(v_a_1451_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
goto v___jp_942_;
}
else
{
v___y_1434_ = v___x_1463_;
goto v___jp_1433_;
}
}
}
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_configFile_1342_);
lean_dec_ref(v_env_938_);
lean_dec(v_name_935_);
lean_dec_ref(v_dir_934_);
v___x_1464_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
v___x_1465_ = lean_apply_2(v_a_940_, v___x_1464_, lean_box(0));
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1478_, lean_object* v_name_1479_, lean_object* v_tmp_1480_, lean_object* v_lang_1481_, lean_object* v_env_1482_, lean_object* v_offline_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
uint8_t v_tmp_boxed_1486_; uint8_t v_lang_boxed_1487_; uint8_t v_offline_boxed_1488_; lean_object* v_res_1489_; 
v_tmp_boxed_1486_ = lean_unbox(v_tmp_1480_);
v_lang_boxed_1487_ = lean_unbox(v_lang_1481_);
v_offline_boxed_1488_ = lean_unbox(v_offline_1483_);
v_res_1489_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1478_, v_name_1479_, v_tmp_boxed_1486_, v_lang_boxed_1487_, v_env_1482_, v_offline_boxed_1488_, v_a_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(lean_object* v___y_1490_, lean_object* v_x_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___redArg(v___y_1490_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1___boxed(lean_object* v___y_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1_spec__1(v___y_1495_, v_x_1496_, v___y_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1500_, lean_object* v_curr_1501_){
_start:
{
lean_object* v_str_1502_; lean_object* v_startInclusive_1503_; lean_object* v_endExclusive_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_str_1502_ = lean_ctor_get(v_s_1500_, 0);
v_startInclusive_1503_ = lean_ctor_get(v_s_1500_, 1);
v_endExclusive_1504_ = lean_ctor_get(v_s_1500_, 2);
v___x_1505_ = lean_nat_add(v_startInclusive_1503_, v_curr_1501_);
lean_inc(v_endExclusive_1504_);
lean_inc(v___x_1505_);
lean_inc_ref(v_str_1502_);
v___x_1506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1506_, 0, v_str_1502_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
lean_ctor_set(v___x_1506_, 2, v_endExclusive_1504_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_nat_sub(v_endExclusive_1504_, v___x_1505_);
v___x_1509_ = lean_nat_dec_eq(v___x_1507_, v___x_1508_);
lean_dec(v___x_1508_);
if (v___x_1509_ == 0)
{
uint32_t v___x_1510_; uint32_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_string_utf8_get_fast(v_str_1502_, v___x_1505_);
v___x_1511_ = 46;
v___x_1512_ = lean_uint32_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_dec(v___x_1505_);
lean_dec(v_curr_1501_);
return v___x_1506_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1513_ = lean_string_utf8_next_fast(v_str_1502_, v___x_1505_);
v___x_1514_ = lean_nat_sub(v___x_1513_, v___x_1505_);
lean_dec(v___x_1505_);
v___x_1515_ = lean_nat_add(v_curr_1501_, v___x_1514_);
lean_dec(v___x_1514_);
v___x_1516_ = lean_nat_dec_lt(v_curr_1501_, v___x_1515_);
lean_dec(v_curr_1501_);
if (v___x_1516_ == 0)
{
lean_dec(v___x_1515_);
return v___x_1506_;
}
else
{
lean_dec_ref(v___x_1506_);
v_curr_1501_ = v___x_1515_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1505_);
lean_dec(v_curr_1501_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1518_, lean_object* v_curr_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1518_, v_curr_1519_);
lean_dec_ref(v_s_1518_);
return v_res_1520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___f_1522_; 
v___x_1521_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1522_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1522_, 0, v___x_1521_);
return v___f_1522_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = 92;
v___x_1524_ = lean_box_uint32(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
v___x_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
return v___x_1527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = 47;
v___x_1529_ = lean_box_uint32(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
v___x_1531_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object* v_s_1533_, lean_object* v_a_1534_, uint8_t v_b_1535_){
_start:
{
lean_object* v_str_1536_; lean_object* v_startInclusive_1537_; lean_object* v_endExclusive_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_str_1536_ = lean_ctor_get(v_s_1533_, 0);
v_startInclusive_1537_ = lean_ctor_get(v_s_1533_, 1);
v_endExclusive_1538_ = lean_ctor_get(v_s_1533_, 2);
v___x_1539_ = lean_nat_sub(v_endExclusive_1538_, v_startInclusive_1537_);
v___x_1540_ = lean_nat_dec_eq(v_a_1534_, v___x_1539_);
lean_dec(v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint32_t v___x_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1541_ = lean_nat_add(v_startInclusive_1537_, v_a_1534_);
lean_dec(v_a_1534_);
v___x_1542_ = lean_string_utf8_get_fast(v_str_1536_, v___x_1541_);
v___f_1543_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
v___x_1544_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
v___x_1545_ = lean_box_uint32(v___x_1542_);
v___x_1546_ = l_List_elem___redArg(v___f_1543_, v___x_1545_, v___x_1544_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_string_utf8_next_fast(v_str_1536_, v___x_1541_);
lean_dec(v___x_1541_);
v___x_1548_ = lean_nat_sub(v___x_1547_, v_startInclusive_1537_);
v_a_1534_ = v___x_1548_;
v_b_1535_ = v___x_1546_;
goto _start;
}
else
{
lean_dec(v___x_1541_);
return v___x_1546_;
}
}
else
{
lean_dec(v_a_1534_);
return v_b_1535_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object* v_s_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_){
_start:
{
uint8_t v_b_boxed_1553_; uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_b_boxed_1553_ = lean_unbox(v_b_1552_);
v_res_1554_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1550_, v_a_1551_, v_b_boxed_1553_);
lean_dec_ref(v_s_1550_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* v_s_1556_){
_start:
{
lean_object* v_searcher_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; 
v_searcher_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = 0;
v___x_1559_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1556_, v_searcher_1557_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_s_1560_){
_start:
{
uint8_t v_res_1561_; lean_object* v_r_1562_; 
v_res_1561_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_s_1560_);
lean_dec_ref(v_s_1560_);
v_r_1562_ = lean_box(v_res_1561_);
return v_r_1562_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___f_1565_; 
v___x_1564_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1565_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1565_, 0, v___x_1564_);
return v___f_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1585_, lean_object* v_a_1586_){
_start:
{
uint8_t v___y_1599_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_string_utf8_byte_size(v_pkgName_1585_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_startInclusive_1619_; lean_object* v_endExclusive_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
lean_inc_ref(v_pkgName_1585_);
v___x_1617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1617_, 0, v_pkgName_1585_);
lean_ctor_set(v___x_1617_, 1, v___x_1615_);
lean_ctor_set(v___x_1617_, 2, v___x_1614_);
v___x_1618_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1617_, v___x_1615_);
lean_dec_ref(v___x_1617_);
v_startInclusive_1619_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_startInclusive_1619_);
v_endExclusive_1620_ = lean_ctor_get(v___x_1618_, 2);
lean_inc(v_endExclusive_1620_);
lean_dec_ref(v___x_1618_);
v___x_1621_ = lean_nat_sub(v_endExclusive_1620_, v_startInclusive_1619_);
lean_dec(v_startInclusive_1619_);
lean_dec(v_endExclusive_1620_);
v___x_1622_ = lean_nat_dec_eq(v___x_1621_, v___x_1615_);
lean_dec(v___x_1621_);
v___y_1599_ = v___x_1622_;
goto v___jp_1598_;
}
else
{
v___y_1599_ = v___x_1616_;
goto v___jp_1598_;
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1589_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1590_ = lean_string_append(v___x_1589_, v_pkgName_1585_);
lean_dec_ref(v_pkgName_1585_);
v___x_1591_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
v___x_1593_ = 3;
v___x_1594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*1, v___x_1593_);
v___x_1595_ = lean_array_get_size(v_a_1586_);
v___x_1596_ = lean_array_push(v_a_1586_, v___x_1594_);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
v___jp_1598_:
{
if (v___y_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = lean_string_utf8_byte_size(v_pkgName_1585_);
lean_inc_ref(v_pkgName_1585_);
v___x_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1602_, 0, v_pkgName_1585_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v___x_1601_);
v___x_1603_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1602_);
lean_dec_ref(v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___f_1604_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1, &l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1);
v___x_1605_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1585_, v___x_1600_);
v___x_1606_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8));
v___x_1607_ = l_List_elem___redArg(v___f_1604_, v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v_a_1586_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1610_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10));
v___x_1611_ = lean_array_get_size(v_a_1586_);
v___x_1612_ = lean_array_push(v_a_1586_, v___x_1610_);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
else
{
goto v___jp_1588_;
}
}
else
{
goto v___jp_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1623_, v_a_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object* v_s_1627_, lean_object* v_inst_1628_, lean_object* v_R_1629_, lean_object* v_a_1630_, uint8_t v_b_1631_, lean_object* v_c_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1627_, v_a_1630_, v_b_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object* v_s_1634_, lean_object* v_inst_1635_, lean_object* v_R_1636_, lean_object* v_a_1637_, lean_object* v_b_1638_, lean_object* v_c_1639_){
_start:
{
uint8_t v_b_boxed_1640_; uint8_t v_res_1641_; lean_object* v_r_1642_; 
v_b_boxed_1640_ = lean_unbox(v_b_1638_);
v_res_1641_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(v_s_1634_, v_inst_1635_, v_R_1636_, v_a_1637_, v_b_boxed_1640_, v_c_1639_);
lean_dec_ref(v_s_1634_);
v_r_1642_ = lean_box(v_res_1641_);
return v_r_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1643_, lean_object* v_dir_1644_, lean_object* v_name_1645_, uint8_t v_tmp_1646_, uint8_t v_lang_1647_, lean_object* v_env_1648_, uint8_t v_offline_1649_){
_start:
{
lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v_a_1685_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v_a_1817_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v_a_1886_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v_a_1918_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; uint8_t v_a_2019_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v_configFile_2051_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v_fst_2090_; lean_object* v_snd_2091_; lean_object* v___y_2099_; lean_object* v___y_2100_; uint8_t v_a_2101_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2123_; lean_object* v___y_2124_; uint8_t v_a_2125_; lean_object* v___y_2143_; uint8_t v___x_2144_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_1654_ = l_Lake_defaultConfigFile;
v___x_2049_ = l_Lake_ConfigLang_fileExtension(v_lang_1647_);
v___x_2050_ = l_System_FilePath_addExtension(v___x_1654_, v___x_2049_);
lean_dec_ref(v___x_2049_);
lean_inc_ref(v_dir_1644_);
v_configFile_2051_ = l_Lake_joinRelative(v_dir_1644_, v___x_2050_);
v___x_2144_ = l_System_FilePath_pathExists(v_configFile_2051_);
v___x_2177_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2178_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2178_ == 0)
{
goto v___jp_2145_;
}
else
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2180_ == 0)
{
if (v___x_2178_ == 0)
{
goto v___jp_2145_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2177_, v___x_2181_, v___x_2182_, v___x_2179_, v_a_1643_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref(v___x_2183_);
goto v___jp_2145_;
}
else
{
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2183_;
}
}
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2177_, v___x_2184_, v___x_2185_, v___x_2179_, v_a_1643_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref(v___x_2186_);
goto v___jp_2145_;
}
else
{
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2186_;
}
}
}
v___jp_1651_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
v___jp_1655_:
{
if (v_offline_1649_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_box(0);
v___x_1660_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1644_);
v___x_1661_ = l_Lake_joinRelative(v_dir_1644_, v___x_1660_);
lean_inc_ref(v___x_1661_);
v___x_1662_ = l_Lake_joinRelative(v___x_1661_, v___x_1654_);
v___x_1663_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1664_ = lean_box(1);
v___x_1665_ = l_Lean_Options_empty;
v___x_1666_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1667_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v___x_1667_, 0, v_env_1648_);
lean_ctor_set(v___x_1667_, 1, v___x_1657_);
lean_ctor_set(v___x_1667_, 2, v_dir_1644_);
lean_ctor_set(v___x_1667_, 3, v___x_1658_);
lean_ctor_set(v___x_1667_, 4, v___x_1659_);
lean_ctor_set(v___x_1667_, 5, v___x_1660_);
lean_ctor_set(v___x_1667_, 6, v___x_1661_);
lean_ctor_set(v___x_1667_, 7, v___x_1654_);
lean_ctor_set(v___x_1667_, 8, v___x_1662_);
lean_ctor_set(v___x_1667_, 9, v___x_1663_);
lean_ctor_set(v___x_1667_, 10, v___x_1664_);
lean_ctor_set(v___x_1667_, 11, v___x_1665_);
lean_ctor_set(v___x_1667_, 12, v___x_1666_);
lean_ctor_set(v___x_1667_, 13, v___x_1666_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*14, v_offline_1649_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*14 + 1, v_offline_1649_);
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*14 + 2, v_offline_1649_);
v___x_1668_ = l_Lean_NameSet_empty;
v___x_1669_ = l_Lake_updateManifest(v___x_1667_, v___x_1668_, v___y_1656_);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v___y_1656_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
v___jp_1672_:
{
if (lean_obj_tag(v___y_1674_) == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1673_);
v___x_1676_ = lean_apply_2(v___y_1673_, v___x_1675_, lean_box(0));
v___y_1656_ = v___y_1673_;
goto v___jp_1655_;
}
else
{
lean_dec_ref(v___y_1674_);
v___y_1656_ = v___y_1673_;
goto v___jp_1655_;
}
}
v___jp_1677_:
{
switch(v_tmp_1646_)
{
case 3:
{
v___y_1673_ = v___y_1679_;
v___y_1674_ = v___y_1678_;
goto v___jp_1672_;
}
case 4:
{
v___y_1673_ = v___y_1679_;
v___y_1674_ = v___y_1678_;
goto v___jp_1672_;
}
default: 
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
v___jp_1682_:
{
if (v_a_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1684_);
v___x_1687_ = lean_apply_2(v___y_1684_, v___x_1686_, lean_box(0));
v___y_1678_ = v___y_1683_;
v___y_1679_ = v___y_1684_;
goto v___jp_1677_;
}
else
{
v___y_1678_ = v___y_1683_;
v___y_1679_ = v___y_1684_;
goto v___jp_1677_;
}
}
v___jp_1688_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1644_);
v___x_1694_ = l_Lake_joinRelative(v_dir_1644_, v___x_1693_);
v___x_1695_ = 4;
v___x_1696_ = lean_io_prim_handle_mk(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1699_ = lean_io_prim_handle_put_str(v_a_1697_, v___x_1698_);
lean_dec(v_a_1697_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
lean_dec_ref(v___x_1699_);
v___x_1700_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1644_);
v___x_1701_ = l_Lake_joinRelative(v_dir_1644_, v___x_1700_);
v___x_1702_ = lean_string_utf8_byte_size(v___y_1689_);
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_nat_dec_eq(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref(v___y_1691_);
v___x_1705_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1706_ = lean_string_append(v___y_1689_, v___x_1705_);
v___x_1707_ = l_IO_FS_writeFile(v___x_1701_, v___x_1706_);
lean_dec_ref(v___x_1706_);
lean_dec_ref(v___x_1701_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref(v___x_1707_);
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1692_;
goto v___jp_1677_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v___y_1690_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1712_ = lean_io_error_to_string(v_a_1708_);
v___x_1713_ = 3;
v___x_1714_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1, v___x_1713_);
v___x_1715_ = lean_apply_2(v___y_1692_, v___x_1714_, lean_box(0));
v___x_1716_ = lean_box(0);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1716_);
v___x_1718_ = v___x_1710_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_githash_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
lean_dec_ref(v___y_1689_);
v_githash_1721_ = lean_ctor_get(v___y_1691_, 1);
lean_inc_ref(v_githash_1721_);
lean_dec_ref(v___y_1691_);
v___x_1722_ = lean_string_utf8_byte_size(v_githash_1721_);
lean_dec_ref(v_githash_1721_);
v___x_1723_ = lean_nat_dec_eq(v___x_1722_, v___x_1703_);
if (v___x_1723_ == 0)
{
uint8_t v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = l_System_FilePath_pathExists(v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1725_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1726_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1726_ == 0)
{
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___y_1692_;
v_a_1685_ = v___x_1724_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_box(0);
v___x_1728_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1728_ == 0)
{
if (v___x_1726_ == 0)
{
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___y_1692_;
v_a_1685_ = v___x_1724_;
goto v___jp_1682_;
}
else
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1692_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1725_, v___x_1729_, v___x_1730_, v___x_1727_, v___y_1692_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref(v___x_1731_);
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___y_1692_;
v_a_1685_ = v___x_1724_;
goto v___jp_1682_;
}
else
{
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1690_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
return v___x_1731_;
}
}
}
else
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((size_t)0ULL);
v___x_1733_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1692_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1725_, v___x_1732_, v___x_1733_, v___x_1727_, v___y_1692_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_dec_ref(v___x_1734_);
v___y_1683_ = v___y_1690_;
v___y_1684_ = v___y_1692_;
v_a_1685_ = v___x_1724_;
goto v___jp_1682_;
}
else
{
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1690_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
return v___x_1734_;
}
}
}
}
else
{
lean_dec_ref(v___x_1701_);
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1692_;
goto v___jp_1677_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v_a_1735_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1737_ = v___x_1699_;
v_isShared_1738_ = v_isSharedCheck_1747_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1699_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1747_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1739_ = lean_io_error_to_string(v_a_1735_);
v___x_1740_ = 3;
v___x_1741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*1, v___x_1740_);
v___x_1742_ = lean_apply_2(v___y_1692_, v___x_1741_, lean_box(0));
v___x_1743_ = lean_box(0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1743_);
v___x_1745_ = v___x_1737_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v_a_1748_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1750_ = v___x_1696_;
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1696_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1752_ = lean_io_error_to_string(v_a_1748_);
v___x_1753_ = 3;
v___x_1754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*1, v___x_1753_);
v___x_1755_ = lean_apply_2(v___y_1692_, v___x_1754_, lean_box(0));
v___x_1756_ = lean_box(0);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1756_);
v___x_1758_ = v___x_1750_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
v___jp_1761_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1763_);
v___x_1767_ = lean_apply_2(v___y_1763_, v___x_1766_, lean_box(0));
v___y_1689_ = v___y_1762_;
v___y_1690_ = v___y_1764_;
v___y_1691_ = v___y_1765_;
v___y_1692_ = v___y_1763_;
goto v___jp_1688_;
}
v___jp_1768_:
{
if (lean_obj_tag(v___y_1773_) == 0)
{
lean_dec_ref(v___y_1773_);
v___y_1689_ = v___y_1769_;
v___y_1690_ = v___y_1771_;
v___y_1691_ = v___y_1772_;
v___y_1692_ = v___y_1770_;
goto v___jp_1688_;
}
else
{
lean_dec_ref(v___y_1773_);
v___y_1762_ = v___y_1769_;
v___y_1763_ = v___y_1770_;
v___y_1764_ = v___y_1771_;
v___y_1765_ = v___y_1772_;
goto v___jp_1761_;
}
}
v___jp_1774_:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = l_Lake_Git_upstreamBranch;
v___x_1780_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1644_);
v___x_1783_ = l_Lake_GitRepo_checkoutBranch(v___x_1779_, v_dir_1644_, v___x_1782_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = lean_array_get_size(v_a_1784_);
v___x_1786_ = lean_nat_dec_lt(v___x_1781_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v_a_1784_);
v___y_1689_ = v___y_1775_;
v___y_1690_ = v___y_1777_;
v___y_1691_ = v___y_1778_;
v___y_1692_ = v___y_1776_;
goto v___jp_1688_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_nat_dec_le(v___x_1785_, v___x_1785_);
if (v___x_1788_ == 0)
{
if (v___x_1786_ == 0)
{
lean_dec(v_a_1784_);
v___y_1689_ = v___y_1775_;
v___y_1690_ = v___y_1777_;
v___y_1691_ = v___y_1778_;
v___y_1692_ = v___y_1776_;
goto v___jp_1688_;
}
else
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = lean_usize_of_nat(v___x_1785_);
lean_inc_ref(v___y_1776_);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1784_, v___x_1789_, v___x_1790_, v___x_1787_, v___y_1776_);
lean_dec(v_a_1784_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref(v___x_1791_);
v___y_1689_ = v___y_1775_;
v___y_1690_ = v___y_1777_;
v___y_1691_ = v___y_1778_;
v___y_1692_ = v___y_1776_;
goto v___jp_1688_;
}
else
{
v___y_1769_ = v___y_1775_;
v___y_1770_ = v___y_1776_;
v___y_1771_ = v___y_1777_;
v___y_1772_ = v___y_1778_;
v___y_1773_ = v___x_1791_;
goto v___jp_1768_;
}
}
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((size_t)0ULL);
v___x_1793_ = lean_usize_of_nat(v___x_1785_);
lean_inc_ref(v___y_1776_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1784_, v___x_1792_, v___x_1793_, v___x_1787_, v___y_1776_);
lean_dec(v_a_1784_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref(v___x_1794_);
v___y_1689_ = v___y_1775_;
v___y_1690_ = v___y_1777_;
v___y_1691_ = v___y_1778_;
v___y_1692_ = v___y_1776_;
goto v___jp_1688_;
}
else
{
v___y_1769_ = v___y_1775_;
v___y_1770_ = v___y_1776_;
v___y_1771_ = v___y_1777_;
v___y_1772_ = v___y_1778_;
v___y_1773_ = v___x_1794_;
goto v___jp_1768_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_a_1795_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1783_);
v___x_1796_ = lean_array_get_size(v_a_1795_);
v___x_1797_ = lean_nat_dec_lt(v___x_1781_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec(v_a_1795_);
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1778_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_nat_dec_le(v___x_1796_, v___x_1796_);
if (v___x_1799_ == 0)
{
if (v___x_1797_ == 0)
{
lean_dec(v_a_1795_);
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1778_;
goto v___jp_1761_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1796_);
lean_inc_ref(v___y_1776_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1795_, v___x_1800_, v___x_1801_, v___x_1798_, v___y_1776_);
lean_dec(v_a_1795_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref(v___x_1802_);
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1778_;
goto v___jp_1761_;
}
else
{
v___y_1769_ = v___y_1775_;
v___y_1770_ = v___y_1776_;
v___y_1771_ = v___y_1777_;
v___y_1772_ = v___y_1778_;
v___y_1773_ = v___x_1802_;
goto v___jp_1768_;
}
}
}
else
{
size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = lean_usize_of_nat(v___x_1796_);
lean_inc_ref(v___y_1776_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1795_, v___x_1803_, v___x_1804_, v___x_1798_, v___y_1776_);
lean_dec(v_a_1795_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_dec_ref(v___x_1805_);
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1778_;
goto v___jp_1761_;
}
else
{
v___y_1769_ = v___y_1775_;
v___y_1770_ = v___y_1776_;
v___y_1771_ = v___y_1777_;
v___y_1772_ = v___y_1778_;
v___y_1773_ = v___x_1805_;
goto v___jp_1768_;
}
}
}
}
}
else
{
v___y_1689_ = v___y_1775_;
v___y_1690_ = v___y_1777_;
v___y_1691_ = v___y_1778_;
v___y_1692_ = v___y_1776_;
goto v___jp_1688_;
}
}
v___jp_1806_:
{
if (lean_obj_tag(v___y_1811_) == 0)
{
lean_dec_ref(v___y_1811_);
v___y_1775_ = v___y_1807_;
v___y_1776_ = v___y_1808_;
v___y_1777_ = v___y_1809_;
v___y_1778_ = v___y_1810_;
goto v___jp_1774_;
}
else
{
lean_dec_ref(v___y_1811_);
v___y_1762_ = v___y_1807_;
v___y_1763_ = v___y_1808_;
v___y_1764_ = v___y_1809_;
v___y_1765_ = v___y_1810_;
goto v___jp_1761_;
}
}
v___jp_1812_:
{
if (v_a_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1644_);
v___x_1820_ = l_Lake_GitRepo_quietInit(v_dir_1644_, v___x_1819_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = lean_array_get_size(v_a_1821_);
v___x_1823_ = lean_nat_dec_lt(v___x_1818_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec(v_a_1821_);
v___y_1775_ = v___y_1813_;
v___y_1776_ = v___y_1814_;
v___y_1777_ = v___y_1815_;
v___y_1778_ = v___y_1816_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_nat_dec_le(v___x_1822_, v___x_1822_);
if (v___x_1825_ == 0)
{
if (v___x_1823_ == 0)
{
lean_dec(v_a_1821_);
v___y_1775_ = v___y_1813_;
v___y_1776_ = v___y_1814_;
v___y_1777_ = v___y_1815_;
v___y_1778_ = v___y_1816_;
goto v___jp_1774_;
}
else
{
size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = lean_usize_of_nat(v___x_1822_);
lean_inc_ref(v___y_1814_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1821_, v___x_1826_, v___x_1827_, v___x_1824_, v___y_1814_);
lean_dec(v_a_1821_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_dec_ref(v___x_1828_);
v___y_1775_ = v___y_1813_;
v___y_1776_ = v___y_1814_;
v___y_1777_ = v___y_1815_;
v___y_1778_ = v___y_1816_;
goto v___jp_1774_;
}
else
{
v___y_1807_ = v___y_1813_;
v___y_1808_ = v___y_1814_;
v___y_1809_ = v___y_1815_;
v___y_1810_ = v___y_1816_;
v___y_1811_ = v___x_1828_;
goto v___jp_1806_;
}
}
}
else
{
size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = lean_usize_of_nat(v___x_1822_);
lean_inc_ref(v___y_1814_);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1821_, v___x_1829_, v___x_1830_, v___x_1824_, v___y_1814_);
lean_dec(v_a_1821_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref(v___x_1831_);
v___y_1775_ = v___y_1813_;
v___y_1776_ = v___y_1814_;
v___y_1777_ = v___y_1815_;
v___y_1778_ = v___y_1816_;
goto v___jp_1774_;
}
else
{
v___y_1807_ = v___y_1813_;
v___y_1808_ = v___y_1814_;
v___y_1809_ = v___y_1815_;
v___y_1810_ = v___y_1816_;
v___y_1811_ = v___x_1831_;
goto v___jp_1806_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_a_1832_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1820_);
v___x_1833_ = lean_array_get_size(v_a_1832_);
v___x_1834_ = lean_nat_dec_lt(v___x_1818_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec(v_a_1832_);
v___y_1762_ = v___y_1813_;
v___y_1763_ = v___y_1814_;
v___y_1764_ = v___y_1815_;
v___y_1765_ = v___y_1816_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_nat_dec_le(v___x_1833_, v___x_1833_);
if (v___x_1836_ == 0)
{
if (v___x_1834_ == 0)
{
lean_dec(v_a_1832_);
v___y_1762_ = v___y_1813_;
v___y_1763_ = v___y_1814_;
v___y_1764_ = v___y_1815_;
v___y_1765_ = v___y_1816_;
goto v___jp_1761_;
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_of_nat(v___x_1833_);
lean_inc_ref(v___y_1814_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1832_, v___x_1837_, v___x_1838_, v___x_1835_, v___y_1814_);
lean_dec(v_a_1832_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref(v___x_1839_);
v___y_1762_ = v___y_1813_;
v___y_1763_ = v___y_1814_;
v___y_1764_ = v___y_1815_;
v___y_1765_ = v___y_1816_;
goto v___jp_1761_;
}
else
{
v___y_1807_ = v___y_1813_;
v___y_1808_ = v___y_1814_;
v___y_1809_ = v___y_1815_;
v___y_1810_ = v___y_1816_;
v___y_1811_ = v___x_1839_;
goto v___jp_1806_;
}
}
}
else
{
size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1833_);
lean_inc_ref(v___y_1814_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_1832_, v___x_1840_, v___x_1841_, v___x_1835_, v___y_1814_);
lean_dec(v_a_1832_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_dec_ref(v___x_1842_);
v___y_1762_ = v___y_1813_;
v___y_1763_ = v___y_1814_;
v___y_1764_ = v___y_1815_;
v___y_1765_ = v___y_1816_;
goto v___jp_1761_;
}
else
{
v___y_1807_ = v___y_1813_;
v___y_1808_ = v___y_1814_;
v___y_1809_ = v___y_1815_;
v___y_1810_ = v___y_1816_;
v___y_1811_ = v___x_1842_;
goto v___jp_1806_;
}
}
}
}
}
else
{
v___y_1689_ = v___y_1813_;
v___y_1690_ = v___y_1815_;
v___y_1691_ = v___y_1816_;
v___y_1692_ = v___y_1814_;
goto v___jp_1688_;
}
}
v___jp_1843_:
{
uint8_t v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
lean_inc_ref(v_dir_1644_);
v___x_1848_ = l_Lake_GitRepo_insideWorkTree(v_dir_1644_);
v___x_1849_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1850_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1850_ == 0)
{
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1846_;
v_a_1817_ = v___x_1848_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1852_ == 0)
{
if (v___x_1850_ == 0)
{
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1846_;
v_a_1817_ = v___x_1848_;
goto v___jp_1812_;
}
else
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((size_t)0ULL);
v___x_1854_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1847_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1849_, v___x_1853_, v___x_1854_, v___x_1851_, v___y_1847_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_dec_ref(v___x_1855_);
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1846_;
v_a_1817_ = v___x_1848_;
goto v___jp_1812_;
}
else
{
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
return v___x_1855_;
}
}
}
else
{
size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1847_);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1849_, v___x_1856_, v___x_1857_, v___x_1851_, v___y_1847_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec_ref(v___x_1858_);
v___y_1813_ = v___y_1844_;
v___y_1814_ = v___y_1847_;
v___y_1815_ = v___y_1845_;
v___y_1816_ = v___y_1846_;
v_a_1817_ = v___x_1848_;
goto v___jp_1812_;
}
else
{
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
return v___x_1858_;
}
}
}
}
v___jp_1859_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_IO_FS_writeFile(v___y_1861_, v___y_1865_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v___y_1861_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_dec_ref(v___x_1866_);
v___y_1844_ = v___y_1860_;
v___y_1845_ = v___y_1862_;
v___y_1846_ = v___y_1863_;
v___y_1847_ = v___y_1864_;
goto v___jp_1843_;
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v_env_1648_);
lean_dec_ref(v_dir_1644_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1879_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1879_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1871_ = lean_io_error_to_string(v_a_1867_);
v___x_1872_ = 3;
v___x_1873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set_uint8(v___x_1873_, sizeof(void*)*1, v___x_1872_);
v___x_1874_ = lean_apply_2(v___y_1864_, v___x_1873_, lean_box(0));
v___x_1875_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1875_);
v___x_1877_ = v___x_1869_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
v___jp_1880_:
{
if (v_a_1886_ == 0)
{
uint8_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = 4;
v___x_1888_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1646_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1645_);
v___x_1890_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1889_);
lean_dec_ref(v___x_1889_);
v___y_1860_ = v___y_1881_;
v___y_1861_ = v___y_1882_;
v___y_1862_ = v___y_1883_;
v___y_1863_ = v___y_1884_;
v___y_1864_ = v___y_1885_;
v___y_1865_ = v___x_1890_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1645_);
v___x_1892_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1891_);
lean_dec_ref(v___x_1891_);
v___y_1860_ = v___y_1881_;
v___y_1861_ = v___y_1882_;
v___y_1862_ = v___y_1883_;
v___y_1863_ = v___y_1884_;
v___y_1864_ = v___y_1885_;
v___y_1865_ = v___x_1892_;
goto v___jp_1859_;
}
}
else
{
lean_dec_ref(v___y_1882_);
lean_dec(v_name_1645_);
v___y_1844_ = v___y_1881_;
v___y_1845_ = v___y_1883_;
v___y_1846_ = v___y_1884_;
v___y_1847_ = v___y_1885_;
goto v___jp_1843_;
}
}
v___jp_1893_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1898_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_1644_);
v___x_1899_ = l_Lake_joinRelative(v_dir_1644_, v___x_1898_);
v___x_1900_ = l_System_FilePath_pathExists(v___x_1899_);
v___x_1901_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1902_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1902_ == 0)
{
v___y_1881_ = v___y_1894_;
v___y_1882_ = v___x_1899_;
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1896_;
v___y_1885_ = v___y_1897_;
v_a_1886_ = v___x_1900_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1904_ == 0)
{
if (v___x_1902_ == 0)
{
v___y_1881_ = v___y_1894_;
v___y_1882_ = v___x_1899_;
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1896_;
v___y_1885_ = v___y_1897_;
v_a_1886_ = v___x_1900_;
goto v___jp_1880_;
}
else
{
size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1897_);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1901_, v___x_1905_, v___x_1906_, v___x_1903_, v___y_1897_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref(v___x_1907_);
v___y_1881_ = v___y_1894_;
v___y_1882_ = v___x_1899_;
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1896_;
v___y_1885_ = v___y_1897_;
v_a_1886_ = v___x_1900_;
goto v___jp_1880_;
}
else
{
lean_dec_ref(v___x_1899_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
return v___x_1907_;
}
}
}
else
{
size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = ((size_t)0ULL);
v___x_1909_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1897_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1901_, v___x_1908_, v___x_1909_, v___x_1903_, v___y_1897_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_dec_ref(v___x_1910_);
v___y_1881_ = v___y_1894_;
v___y_1882_ = v___x_1899_;
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1896_;
v___y_1885_ = v___y_1897_;
v_a_1886_ = v___x_1900_;
goto v___jp_1880_;
}
else
{
lean_dec_ref(v___x_1899_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
return v___x_1910_;
}
}
}
}
v___jp_1911_:
{
if (v_a_1918_ == 0)
{
uint8_t v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = 1;
v___x_1920_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1646_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1912_);
v___x_1922_ = l_IO_FS_writeFile(v___y_1914_, v___x_1921_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___y_1914_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_dec_ref(v___x_1922_);
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1915_;
v___y_1896_ = v___y_1917_;
v___y_1897_ = v___y_1916_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1935_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1935_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1927_ = lean_io_error_to_string(v_a_1923_);
v___x_1928_ = 3;
v___x_1929_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set_uint8(v___x_1929_, sizeof(void*)*1, v___x_1928_);
v___x_1930_ = lean_apply_2(v___y_1916_, v___x_1929_, lean_box(0));
v___x_1931_ = lean_box(0);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1931_);
v___x_1933_ = v___x_1925_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v___y_1912_);
v___x_1936_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1937_ = l_IO_FS_writeFile(v___y_1914_, v___x_1936_);
lean_dec_ref(v___y_1914_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec_ref(v___x_1937_);
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1915_;
v___y_1896_ = v___y_1917_;
v___y_1897_ = v___y_1916_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1950_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1950_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1942_ = lean_io_error_to_string(v_a_1938_);
v___x_1943_ = 3;
v___x_1944_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set_uint8(v___x_1944_, sizeof(void*)*1, v___x_1943_);
v___x_1945_ = lean_apply_2(v___y_1916_, v___x_1944_, lean_box(0));
v___x_1946_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1946_);
v___x_1948_ = v___x_1940_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1912_);
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1915_;
v___y_1896_ = v___y_1917_;
v___y_1897_ = v___y_1916_;
goto v___jp_1893_;
}
}
v___jp_1951_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1957_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1644_);
v___x_1958_ = l_Lake_joinRelative(v_dir_1644_, v___x_1957_);
v___x_1959_ = l_System_FilePath_pathExists(v___x_1958_);
v___x_1960_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1961_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1961_ == 0)
{
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1958_;
v___y_1915_ = v___y_1954_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v_a_1918_ = v___x_1959_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1963_ == 0)
{
if (v___x_1961_ == 0)
{
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1958_;
v___y_1915_ = v___y_1954_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v_a_1918_ = v___x_1959_;
goto v___jp_1911_;
}
else
{
size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1955_);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1960_, v___x_1964_, v___x_1965_, v___x_1962_, v___y_1955_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_dec_ref(v___x_1966_);
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1958_;
v___y_1915_ = v___y_1954_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v_a_1918_ = v___x_1959_;
goto v___jp_1911_;
}
else
{
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
return v___x_1966_;
}
}
}
else
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v___y_1955_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_1960_, v___x_1967_, v___x_1968_, v___x_1962_, v___y_1955_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref(v___x_1969_);
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1958_;
v___y_1915_ = v___y_1954_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v_a_1918_ = v___x_1959_;
goto v___jp_1911_;
}
else
{
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
return v___x_1969_;
}
}
}
}
v___jp_1970_:
{
switch(v_tmp_1646_)
{
case 0:
{
v___y_1952_ = v___y_1971_;
v___y_1953_ = v___y_1972_;
v___y_1954_ = v___y_1973_;
v___y_1955_ = v___y_1975_;
v___y_1956_ = v___y_1974_;
goto v___jp_1951_;
}
case 1:
{
v___y_1952_ = v___y_1971_;
v___y_1953_ = v___y_1972_;
v___y_1954_ = v___y_1973_;
v___y_1955_ = v___y_1975_;
v___y_1956_ = v___y_1974_;
goto v___jp_1951_;
}
default: 
{
lean_dec(v___y_1971_);
v___y_1894_ = v___y_1972_;
v___y_1895_ = v___y_1973_;
v___y_1896_ = v___y_1974_;
v___y_1897_ = v___y_1975_;
goto v___jp_1893_;
}
}
}
v___jp_1976_:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_IO_FS_writeFile(v___y_1981_, v___y_1983_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_dec_ref(v___x_1984_);
v___y_1971_ = v___y_1977_;
v___y_1972_ = v___y_1978_;
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
v___y_1975_ = v___y_1982_;
goto v___jp_1970_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1989_ = lean_io_error_to_string(v_a_1985_);
v___x_1990_ = 3;
v___x_1991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1, v___x_1990_);
v___x_1992_ = lean_apply_2(v___y_1982_, v___x_1991_, lean_box(0));
v___x_1993_ = lean_box(0);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1993_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
v___jp_1998_:
{
uint8_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = 4;
v___x_2006_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1646_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = 1;
lean_inc(v___y_1999_);
v___x_2008_ = l_Lean_Name_toString(v___y_1999_, v___x_2007_);
lean_inc(v___y_1999_);
v___x_2009_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_2008_, v___y_1999_);
lean_dec_ref(v___x_2008_);
v___y_1977_ = v___y_1999_;
v___y_1978_ = v___y_2000_;
v___y_1979_ = v___y_2001_;
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2002_;
v___y_1982_ = v___y_2004_;
v___y_1983_ = v___x_2009_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2010_; 
lean_inc(v___y_1999_);
v___x_2010_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1999_);
v___y_1977_ = v___y_1999_;
v___y_1978_ = v___y_2000_;
v___y_1979_ = v___y_2001_;
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2002_;
v___y_1982_ = v___y_2004_;
v___y_1983_ = v___x_2010_;
goto v___jp_1976_;
}
}
v___jp_2011_:
{
if (v_a_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = l_IO_FS_createDirAll(v___y_2015_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v___x_2020_);
v___x_2021_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_2022_ = l_IO_FS_writeFile(v___y_2014_, v___x_2021_);
lean_dec_ref(v___y_2014_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref(v___x_2022_);
v___y_1999_ = v___y_2012_;
v___y_2000_ = v___y_2013_;
v___y_2001_ = v___y_2016_;
v___y_2002_ = v___y_2018_;
v___y_2003_ = v___y_2017_;
v___y_2004_ = v_a_1643_;
goto v___jp_1998_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2035_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2035_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2027_ = lean_io_error_to_string(v_a_2023_);
v___x_2028_ = 3;
v___x_2029_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*1, v___x_2028_);
v___x_2030_ = lean_apply_2(v_a_1643_, v___x_2029_, lean_box(0));
v___x_2031_ = lean_box(0);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2031_);
v___x_2033_ = v___x_2025_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_2036_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2038_ = v___x_2020_;
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2020_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2048_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2040_ = lean_io_error_to_string(v_a_2036_);
v___x_2041_ = 3;
v___x_2042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1, v___x_2041_);
v___x_2043_ = lean_apply_2(v_a_1643_, v___x_2042_, lean_box(0));
v___x_2044_ = lean_box(0);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2044_);
v___x_2046_ = v___x_2038_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_dec_ref(v___y_2015_);
lean_dec_ref(v___y_2014_);
v___y_1999_ = v___y_2012_;
v___y_2000_ = v___y_2013_;
v___y_2001_ = v___y_2016_;
v___y_2002_ = v___y_2018_;
v___y_2003_ = v___y_2017_;
v___y_2004_ = v_a_1643_;
goto v___jp_1998_;
}
}
v___jp_2052_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_inc(v___y_2057_);
lean_inc(v___y_2053_);
lean_inc(v_name_1645_);
v___x_2058_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1646_, v_lang_1647_, v_name_1645_, v___y_2053_, v___y_2057_);
v___x_2059_ = l_IO_FS_writeFile(v_configFile_2051_, v___x_2058_);
lean_dec_ref(v___x_2058_);
lean_dec_ref(v_configFile_2051_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_dec_ref(v___x_2059_);
if (lean_obj_tag(v___y_2055_) == 1)
{
lean_object* v_val_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_val_2060_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_val_2060_);
lean_dec_ref(v___y_2055_);
v___x_2061_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
lean_inc(v_val_2060_);
v___x_2062_ = l_System_FilePath_withExtension(v_val_2060_, v___x_2061_);
v___x_2063_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_2062_);
v___x_2064_ = l_Lake_joinRelative(v___x_2062_, v___x_2063_);
v___x_2065_ = l_System_FilePath_pathExists(v___x_2064_);
v___x_2066_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2067_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2067_ == 0)
{
v___y_2012_ = v___y_2053_;
v___y_2013_ = v___y_2054_;
v___y_2014_ = v___x_2064_;
v___y_2015_ = v___x_2062_;
v___y_2016_ = v___y_2057_;
v___y_2017_ = v___y_2056_;
v___y_2018_ = v_val_2060_;
v_a_2019_ = v___x_2065_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2069_ == 0)
{
if (v___x_2067_ == 0)
{
v___y_2012_ = v___y_2053_;
v___y_2013_ = v___y_2054_;
v___y_2014_ = v___x_2064_;
v___y_2015_ = v___x_2062_;
v___y_2016_ = v___y_2057_;
v___y_2017_ = v___y_2056_;
v___y_2018_ = v_val_2060_;
v_a_2019_ = v___x_2065_;
goto v___jp_2011_;
}
else
{
size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2066_, v___x_2070_, v___x_2071_, v___x_2068_, v_a_1643_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec_ref(v___x_2072_);
v___y_2012_ = v___y_2053_;
v___y_2013_ = v___y_2054_;
v___y_2014_ = v___x_2064_;
v___y_2015_ = v___x_2062_;
v___y_2016_ = v___y_2057_;
v___y_2017_ = v___y_2056_;
v___y_2018_ = v_val_2060_;
v_a_2019_ = v___x_2065_;
goto v___jp_2011_;
}
else
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2062_);
lean_dec(v_val_2060_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2072_;
}
}
}
else
{
size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2066_, v___x_2073_, v___x_2074_, v___x_2068_, v_a_1643_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref(v___x_2075_);
v___y_2012_ = v___y_2053_;
v___y_2013_ = v___y_2054_;
v___y_2014_ = v___x_2064_;
v___y_2015_ = v___x_2062_;
v___y_2016_ = v___y_2057_;
v___y_2017_ = v___y_2056_;
v___y_2018_ = v_val_2060_;
v_a_2019_ = v___x_2065_;
goto v___jp_2011_;
}
else
{
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2062_);
lean_dec(v_val_2060_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2075_;
}
}
}
}
else
{
lean_dec(v___y_2055_);
v___y_1971_ = v___y_2053_;
v___y_1972_ = v___y_2054_;
v___y_1973_ = v___y_2057_;
v___y_1974_ = v___y_2056_;
v___y_1975_ = v_a_1643_;
goto v___jp_1970_;
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v_a_2076_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2078_ = v___x_2059_;
v_isShared_2079_ = v_isSharedCheck_2088_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2059_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2088_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2080_ = lean_io_error_to_string(v_a_2076_);
v___x_2081_ = 3;
v___x_2082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1, v___x_2081_);
v___x_2083_ = lean_apply_2(v_a_1643_, v___x_2082_, lean_box(0));
v___x_2084_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2084_);
v___x_2086_ = v___x_2078_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
v___jp_2089_:
{
lean_object* v_lean_2092_; lean_object* v_toolchain_2093_; lean_object* v___x_2094_; 
v_lean_2092_ = lean_ctor_get(v_env_1648_, 1);
v_toolchain_2093_ = lean_ctor_get(v_env_1648_, 18);
lean_inc_ref(v_toolchain_2093_);
v___x_2094_ = l_Lake_ToolchainVer_ofString(v_toolchain_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_ver_2095_; lean_object* v___x_2096_; 
v_ver_2095_ = lean_ctor_get(v___x_2094_, 1);
lean_inc_ref(v_ver_2095_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_ver_2095_);
lean_inc_ref(v_lean_2092_);
lean_inc_ref(v_toolchain_2093_);
v___y_2053_ = v_fst_2090_;
v___y_2054_ = v_toolchain_2093_;
v___y_2055_ = v_snd_2091_;
v___y_2056_ = v_lean_2092_;
v___y_2057_ = v___x_2096_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2097_; 
lean_dec_ref(v___x_2094_);
v___x_2097_ = lean_box(0);
lean_inc_ref(v_lean_2092_);
lean_inc_ref(v_toolchain_2093_);
v___y_2053_ = v_fst_2090_;
v___y_2054_ = v_toolchain_2093_;
v___y_2055_ = v_snd_2091_;
v___y_2056_ = v_lean_2092_;
v___y_2057_ = v___x_2097_;
goto v___jp_2052_;
}
}
v___jp_2098_:
{
if (v_a_2101_ == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___y_2099_);
v_fst_2090_ = v___y_2100_;
v_snd_2091_ = v___x_2102_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2103_; 
lean_dec_ref(v___y_2099_);
v___x_2103_ = lean_box(0);
v_fst_2090_ = v___y_2100_;
v_snd_2091_ = v___x_2103_;
goto v___jp_2089_;
}
}
v___jp_2104_:
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
lean_dec_ref(v___y_2106_);
lean_inc(v_name_1645_);
v___x_2108_ = l_Lake_toUpperCamelCase(v_name_1645_);
lean_inc(v___x_2108_);
v___x_2109_ = l_Lean_modToFilePath(v_dir_1644_, v___x_2108_, v___y_2105_);
lean_dec_ref(v___y_2105_);
v___x_2110_ = l_System_FilePath_pathExists(v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2112_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2112_ == 0)
{
v___y_2099_ = v___x_2109_;
v___y_2100_ = v___x_2108_;
v_a_2101_ = v___x_2110_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2114_ == 0)
{
if (v___x_2112_ == 0)
{
v___y_2099_ = v___x_2109_;
v___y_2100_ = v___x_2108_;
v_a_2101_ = v___x_2110_;
goto v___jp_2098_;
}
else
{
size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2111_, v___x_2115_, v___x_2116_, v___x_2113_, v_a_1643_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref(v___x_2117_);
v___y_2099_ = v___x_2109_;
v___y_2100_ = v___x_2108_;
v_a_2101_ = v___x_2110_;
goto v___jp_2098_;
}
else
{
lean_dec_ref(v___x_2109_);
lean_dec(v___x_2108_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2117_;
}
}
}
else
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2111_, v___x_2118_, v___x_2119_, v___x_2113_, v_a_1643_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_dec_ref(v___x_2120_);
v___y_2099_ = v___x_2109_;
v___y_2100_ = v___x_2108_;
v_a_2101_ = v___x_2110_;
goto v___jp_2098_;
}
else
{
lean_dec_ref(v___x_2109_);
lean_dec(v___x_2108_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2121_; 
lean_dec_ref(v___y_2105_);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___y_2106_);
lean_inc(v_name_1645_);
v_fst_2090_ = v_name_1645_;
v_snd_2091_ = v___x_2121_;
goto v___jp_2089_;
}
}
v___jp_2122_:
{
uint8_t v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = 1;
v___x_2127_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1646_, v___x_2126_);
if (v___x_2127_ == 0)
{
v___y_2105_ = v___y_2123_;
v___y_2106_ = v___y_2124_;
v___y_2107_ = v_a_2125_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v___y_2123_;
v___y_2106_ = v___y_2124_;
v___y_2107_ = v___x_2127_;
goto v___jp_2104_;
}
}
v___jp_2128_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2129_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_1645_);
v___x_2130_ = l_Lean_modToFilePath(v_dir_1644_, v_name_1645_, v___x_2129_);
v___x_2131_ = l_System_FilePath_pathExists(v___x_2130_);
v___x_2132_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2133_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2133_ == 0)
{
v___y_2123_ = v___x_2129_;
v___y_2124_ = v___x_2130_;
v_a_2125_ = v___x_2131_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2135_ == 0)
{
if (v___x_2133_ == 0)
{
v___y_2123_ = v___x_2129_;
v___y_2124_ = v___x_2130_;
v_a_2125_ = v___x_2131_;
goto v___jp_2122_;
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2132_, v___x_2136_, v___x_2137_, v___x_2134_, v_a_1643_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_dec_ref(v___x_2138_);
v___y_2123_ = v___x_2129_;
v___y_2124_ = v___x_2130_;
v_a_2125_ = v___x_2131_;
goto v___jp_2122_;
}
else
{
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2138_;
}
}
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
lean_inc_ref(v_a_1643_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v___x_2132_, v___x_2139_, v___x_2140_, v___x_2134_, v_a_1643_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref(v___x_2141_);
v___y_2123_ = v___x_2129_;
v___y_2124_ = v___x_2130_;
v_a_2125_ = v___x_2131_;
goto v___jp_2122_;
}
else
{
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___x_2141_;
}
}
}
}
v___jp_2142_:
{
if (lean_obj_tag(v___y_2143_) == 0)
{
lean_dec_ref(v___y_2143_);
goto v___jp_2128_;
}
else
{
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
return v___y_2143_;
}
}
v___jp_2145_:
{
if (v___x_2144_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1644_);
v___x_2148_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1644_, v_tmp_1646_, v___x_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = lean_array_get_size(v_a_2149_);
v___x_2151_ = lean_nat_dec_lt(v___x_2146_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec(v_a_2149_);
goto v___jp_2128_;
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_nat_dec_le(v___x_2150_, v___x_2150_);
if (v___x_2153_ == 0)
{
if (v___x_2151_ == 0)
{
lean_dec(v_a_2149_);
goto v___jp_2128_;
}
else
{
size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((size_t)0ULL);
v___x_2155_ = lean_usize_of_nat(v___x_2150_);
lean_inc_ref(v_a_1643_);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2149_, v___x_2154_, v___x_2155_, v___x_2152_, v_a_1643_);
lean_dec(v_a_2149_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_dec_ref(v___x_2156_);
goto v___jp_2128_;
}
else
{
v___y_2143_ = v___x_2156_;
goto v___jp_2142_;
}
}
}
else
{
size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = lean_usize_of_nat(v___x_2150_);
lean_inc_ref(v_a_1643_);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2149_, v___x_2157_, v___x_2158_, v___x_2152_, v_a_1643_);
lean_dec(v_a_2149_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref(v___x_2159_);
goto v___jp_2128_;
}
else
{
v___y_2143_ = v___x_2159_;
goto v___jp_2142_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2148_);
v___x_2161_ = lean_array_get_size(v_a_2160_);
v___x_2162_ = lean_nat_dec_lt(v___x_2146_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v_a_2160_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_nat_dec_le(v___x_2161_, v___x_2161_);
if (v___x_2166_ == 0)
{
if (v___x_2162_ == 0)
{
lean_dec(v_a_2160_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
goto v___jp_1651_;
}
else
{
size_t v___x_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = lean_usize_of_nat(v___x_2161_);
lean_inc_ref(v_a_1643_);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2160_, v___x_2167_, v___x_2168_, v___x_2165_, v_a_1643_);
lean_dec(v_a_2160_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
goto v___jp_1651_;
}
else
{
v___y_2143_ = v___x_2169_;
goto v___jp_2142_;
}
}
}
else
{
size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((size_t)0ULL);
v___x_2171_ = lean_usize_of_nat(v___x_2161_);
lean_inc_ref(v_a_1643_);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2160_, v___x_2170_, v___x_2171_, v___x_2165_, v_a_1643_);
lean_dec(v_a_2160_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
lean_dec_ref(v_a_1643_);
goto v___jp_1651_;
}
else
{
v___y_2143_ = v___x_2172_;
goto v___jp_2142_;
}
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v_configFile_2051_);
lean_dec_ref(v_env_1648_);
lean_dec(v_name_1645_);
lean_dec_ref(v_dir_1644_);
v___x_2173_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
v___x_2174_ = lean_apply_2(v_a_1643_, v___x_2173_, lean_box(0));
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2187_, lean_object* v_dir_2188_, lean_object* v_name_2189_, lean_object* v_tmp_2190_, lean_object* v_lang_2191_, lean_object* v_env_2192_, lean_object* v_offline_2193_, lean_object* v_a_2194_){
_start:
{
uint8_t v_tmp_boxed_2195_; uint8_t v_lang_boxed_2196_; uint8_t v_offline_boxed_2197_; lean_object* v_res_2198_; 
v_tmp_boxed_2195_ = lean_unbox(v_tmp_2190_);
v_lang_boxed_2196_ = lean_unbox(v_lang_2191_);
v_offline_boxed_2197_ = lean_unbox(v_offline_2193_);
v_res_2198_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2187_, v_dir_2188_, v_name_2189_, v_tmp_boxed_2195_, v_lang_boxed_2196_, v_env_2192_, v_offline_boxed_2197_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2200_, uint8_t v_tmp_2201_, uint8_t v_lang_2202_, lean_object* v_env_2203_, lean_object* v_cwd_2204_, uint8_t v_offline_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___y_2212_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v_a_2233_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2269_ = lean_string_dec_eq(v_name_2200_, v___x_2268_);
if (v___x_2269_ == 0)
{
v_a_2233_ = v_name_2200_;
goto v___jp_2232_;
}
else
{
lean_object* v___x_2270_; 
lean_dec_ref(v_name_2200_);
lean_inc_ref(v_cwd_2204_);
v___x_2270_ = lean_io_realpath(v_cwd_2204_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2288_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2288_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2288_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; 
lean_inc(v_a_2271_);
v___x_2275_ = l_System_FilePath_fileName(v_a_2271_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
v___x_2276_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2277_ = lean_string_append(v___x_2276_, v_a_2271_);
lean_dec(v_a_2271_);
v___x_2278_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
v___x_2280_ = 3;
v___x_2281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*1, v___x_2280_);
v___x_2282_ = lean_apply_2(v_a_2206_, v___x_2281_, lean_box(0));
v___x_2283_ = lean_box(0);
if (v_isShared_2274_ == 0)
{
lean_ctor_set_tag(v___x_2273_, 1);
lean_ctor_set(v___x_2273_, 0, v___x_2283_);
v___x_2285_ = v___x_2273_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v_val_2287_; 
lean_del_object(v___x_2273_);
lean_dec(v_a_2271_);
v_val_2287_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2287_);
lean_dec_ref(v___x_2275_);
v_a_2233_ = v_val_2287_;
goto v___jp_2232_;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
v_a_2289_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2291_ = v___x_2270_;
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2270_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2293_ = lean_io_error_to_string(v_a_2289_);
v___x_2294_ = 3;
v___x_2295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
v___x_2296_ = lean_apply_2(v_a_2206_, v___x_2295_, lean_box(0));
v___x_2297_ = lean_box(0);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2297_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
v___jp_2208_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
v___jp_2211_:
{
lean_object* v___x_2213_; 
lean_inc_ref(v_cwd_2204_);
v___x_2213_ = l_IO_FS_createDirAll(v_cwd_2204_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v___x_2213_);
v___x_2214_ = l_Lake_stringToLegalOrSimpleName(v___y_2212_);
v___x_2215_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2206_, v_cwd_2204_, v___x_2214_, v_tmp_2201_, v_lang_2202_, v_env_2203_, v_offline_2205_);
return v___x_2215_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
v_a_2216_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2218_ = v___x_2213_;
v_isShared_2219_ = v_isSharedCheck_2228_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2213_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2228_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2220_ = lean_io_error_to_string(v_a_2216_);
v___x_2221_ = 3;
v___x_2222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2221_);
v___x_2223_ = lean_apply_2(v_a_2206_, v___x_2222_, lean_box(0));
v___x_2224_ = lean_box(0);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2224_);
v___x_2226_ = v___x_2218_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
v___jp_2229_:
{
if (lean_obj_tag(v___y_2231_) == 0)
{
lean_dec_ref(v___y_2231_);
v___y_2212_ = v___y_2230_;
goto v___jp_2211_;
}
else
{
lean_dec_ref(v___y_2230_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
return v___y_2231_;
}
}
v___jp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_str_2238_; lean_object* v_startInclusive_2239_; lean_object* v_endExclusive_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_string_utf8_byte_size(v_a_2233_);
v___x_2236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2233_);
lean_ctor_set(v___x_2236_, 1, v___x_2234_);
lean_ctor_set(v___x_2236_, 2, v___x_2235_);
v___x_2237_ = l_String_Slice_trimAscii(v___x_2236_);
lean_dec_ref(v___x_2236_);
v_str_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc_ref(v_str_2238_);
v_startInclusive_2239_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_startInclusive_2239_);
v_endExclusive_2240_ = lean_ctor_get(v___x_2237_, 2);
lean_inc(v_endExclusive_2240_);
lean_dec_ref(v___x_2237_);
v___x_2241_ = lean_string_utf8_extract(v_str_2238_, v_startInclusive_2239_, v_endExclusive_2240_);
lean_dec(v_endExclusive_2240_);
lean_dec(v_startInclusive_2239_);
lean_dec_ref(v_str_2238_);
v___x_2242_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2241_);
v___x_2243_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2241_, v___x_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = lean_array_get_size(v_a_2244_);
v___x_2246_ = lean_nat_dec_lt(v___x_2234_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_dec(v_a_2244_);
v___y_2212_ = v___x_2241_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_nat_dec_le(v___x_2245_, v___x_2245_);
if (v___x_2248_ == 0)
{
if (v___x_2246_ == 0)
{
lean_dec(v_a_2244_);
v___y_2212_ = v___x_2241_;
goto v___jp_2211_;
}
else
{
size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = ((size_t)0ULL);
v___x_2250_ = lean_usize_of_nat(v___x_2245_);
lean_inc_ref(v_a_2206_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2244_, v___x_2249_, v___x_2250_, v___x_2247_, v_a_2206_);
lean_dec(v_a_2244_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_dec_ref(v___x_2251_);
v___y_2212_ = v___x_2241_;
goto v___jp_2211_;
}
else
{
v___y_2230_ = v___x_2241_;
v___y_2231_ = v___x_2251_;
goto v___jp_2229_;
}
}
}
else
{
size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = lean_usize_of_nat(v___x_2245_);
lean_inc_ref(v_a_2206_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2244_, v___x_2252_, v___x_2253_, v___x_2247_, v_a_2206_);
lean_dec(v_a_2244_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_dec_ref(v___x_2254_);
v___y_2212_ = v___x_2241_;
goto v___jp_2211_;
}
else
{
v___y_2230_ = v___x_2241_;
v___y_2231_ = v___x_2254_;
goto v___jp_2229_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_a_2255_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_a_2255_);
lean_dec_ref(v___x_2243_);
v___x_2256_ = lean_array_get_size(v_a_2255_);
v___x_2257_ = lean_nat_dec_lt(v___x_2234_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_nat_dec_le(v___x_2256_, v___x_2256_);
if (v___x_2261_ == 0)
{
if (v___x_2257_ == 0)
{
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
goto v___jp_2208_;
}
else
{
size_t v___x_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = lean_usize_of_nat(v___x_2256_);
lean_inc_ref(v_a_2206_);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2255_, v___x_2262_, v___x_2263_, v___x_2260_, v_a_2206_);
lean_dec(v_a_2255_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_dec_ref(v___x_2264_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
goto v___jp_2208_;
}
else
{
v___y_2230_ = v___x_2241_;
v___y_2231_ = v___x_2264_;
goto v___jp_2229_;
}
}
}
else
{
size_t v___x_2265_; size_t v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = ((size_t)0ULL);
v___x_2266_ = lean_usize_of_nat(v___x_2256_);
lean_inc_ref(v_a_2206_);
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2255_, v___x_2265_, v___x_2266_, v___x_2260_, v_a_2206_);
lean_dec(v_a_2255_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec_ref(v___x_2267_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_cwd_2204_);
lean_dec_ref(v_env_2203_);
goto v___jp_2208_;
}
else
{
v___y_2230_ = v___x_2241_;
v___y_2231_ = v___x_2267_;
goto v___jp_2229_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2302_, lean_object* v_tmp_2303_, lean_object* v_lang_2304_, lean_object* v_env_2305_, lean_object* v_cwd_2306_, lean_object* v_offline_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v_tmp_boxed_2310_; uint8_t v_lang_boxed_2311_; uint8_t v_offline_boxed_2312_; lean_object* v_res_2313_; 
v_tmp_boxed_2310_ = lean_unbox(v_tmp_2303_);
v_lang_boxed_2311_ = lean_unbox(v_lang_2304_);
v_offline_boxed_2312_ = lean_unbox(v_offline_2307_);
v_res_2313_ = l_Lake_init(v_name_2302_, v_tmp_boxed_2310_, v_lang_boxed_2311_, v_env_2305_, v_cwd_2306_, v_offline_boxed_2312_, v_a_2308_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2314_, uint8_t v_tmp_2315_, uint8_t v_lang_2316_, lean_object* v_env_2317_, lean_object* v_cwd_2318_, uint8_t v_offline_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_str_2329_; lean_object* v_startInclusive_2330_; lean_object* v_endExclusive_2331_; lean_object* v_name_2332_; lean_object* v___y_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_string_utf8_byte_size(v_name_2314_);
v___x_2327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2327_, 0, v_name_2314_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2326_);
v___x_2328_ = l_String_Slice_trimAscii(v___x_2327_);
lean_dec_ref(v___x_2327_);
v_str_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_str_2329_);
v_startInclusive_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_startInclusive_2330_);
v_endExclusive_2331_ = lean_ctor_get(v___x_2328_, 2);
lean_inc(v_endExclusive_2331_);
lean_dec_ref(v___x_2328_);
v_name_2332_ = lean_string_utf8_extract(v_str_2329_, v_startInclusive_2330_, v_endExclusive_2331_);
lean_dec(v_endExclusive_2331_);
lean_dec(v_startInclusive_2330_);
lean_dec_ref(v_str_2329_);
v___x_2354_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2332_);
v___x_2355_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2332_, v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 1);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_array_get_size(v_a_2356_);
v___x_2358_ = lean_nat_dec_lt(v___x_2325_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec(v_a_2356_);
goto v___jp_2333_;
}
else
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_nat_dec_le(v___x_2357_, v___x_2357_);
if (v___x_2360_ == 0)
{
if (v___x_2358_ == 0)
{
lean_dec(v_a_2356_);
goto v___jp_2333_;
}
else
{
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_of_nat(v___x_2357_);
lean_inc_ref(v_a_2320_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2356_, v___x_2361_, v___x_2362_, v___x_2359_, v_a_2320_);
lean_dec(v_a_2356_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref(v___x_2363_);
goto v___jp_2333_;
}
else
{
v___y_2353_ = v___x_2363_;
goto v___jp_2352_;
}
}
}
else
{
size_t v___x_2364_; size_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = lean_usize_of_nat(v___x_2357_);
lean_inc_ref(v_a_2320_);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2356_, v___x_2364_, v___x_2365_, v___x_2359_, v_a_2320_);
lean_dec(v_a_2356_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_dec_ref(v___x_2366_);
goto v___jp_2333_;
}
else
{
v___y_2353_ = v___x_2366_;
goto v___jp_2352_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_a_2367_ = lean_ctor_get(v___x_2355_, 1);
lean_inc(v_a_2367_);
lean_dec_ref(v___x_2355_);
v___x_2368_ = lean_array_get_size(v_a_2367_);
v___x_2369_ = lean_nat_dec_lt(v___x_2325_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_dec(v_a_2367_);
lean_dec_ref(v_name_2332_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_cwd_2318_);
lean_dec_ref(v_env_2317_);
v___x_2370_ = lean_box(0);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
else
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_nat_dec_le(v___x_2368_, v___x_2368_);
if (v___x_2373_ == 0)
{
if (v___x_2369_ == 0)
{
lean_dec(v_a_2367_);
lean_dec_ref(v_name_2332_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_cwd_2318_);
lean_dec_ref(v_env_2317_);
goto v___jp_2322_;
}
else
{
size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = lean_usize_of_nat(v___x_2368_);
lean_inc_ref(v_a_2320_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2367_, v___x_2374_, v___x_2375_, v___x_2372_, v_a_2320_);
lean_dec(v_a_2367_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_dec_ref(v___x_2376_);
lean_dec_ref(v_name_2332_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_cwd_2318_);
lean_dec_ref(v_env_2317_);
goto v___jp_2322_;
}
else
{
v___y_2353_ = v___x_2376_;
goto v___jp_2352_;
}
}
}
else
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = lean_usize_of_nat(v___x_2368_);
lean_inc_ref(v_a_2320_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__1(v_a_2367_, v___x_2377_, v___x_2378_, v___x_2372_, v_a_2320_);
lean_dec(v_a_2367_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_name_2332_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_cwd_2318_);
lean_dec_ref(v_env_2317_);
goto v___jp_2322_;
}
else
{
v___y_2353_ = v___x_2379_;
goto v___jp_2352_;
}
}
}
}
v___jp_2322_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
v___jp_2333_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = l_Lake_stringToLegalOrSimpleName(v_name_2332_);
lean_inc(v___x_2334_);
v___x_2335_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2334_);
v___x_2336_ = l_Lake_joinRelative(v_cwd_2318_, v___x_2335_);
lean_inc_ref(v___x_2336_);
v___x_2337_ = l_IO_FS_createDirAll(v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v___x_2338_; 
lean_dec_ref(v___x_2337_);
v___x_2338_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2320_, v___x_2336_, v___x_2334_, v_tmp_2315_, v_lang_2316_, v_env_2317_, v_offline_2319_);
return v___x_2338_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___x_2336_);
lean_dec(v___x_2334_);
lean_dec_ref(v_env_2317_);
v_a_2339_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2341_ = v___x_2337_;
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2343_ = lean_io_error_to_string(v_a_2339_);
v___x_2344_ = 3;
v___x_2345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*1, v___x_2344_);
v___x_2346_ = lean_apply_2(v_a_2320_, v___x_2345_, lean_box(0));
v___x_2347_ = lean_box(0);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2347_);
v___x_2349_ = v___x_2341_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
v___jp_2352_:
{
if (lean_obj_tag(v___y_2353_) == 0)
{
lean_dec_ref(v___y_2353_);
goto v___jp_2333_;
}
else
{
lean_dec_ref(v_name_2332_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_cwd_2318_);
lean_dec_ref(v_env_2317_);
return v___y_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2380_, lean_object* v_tmp_2381_, lean_object* v_lang_2382_, lean_object* v_env_2383_, lean_object* v_cwd_2384_, lean_object* v_offline_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
uint8_t v_tmp_boxed_2388_; uint8_t v_lang_boxed_2389_; uint8_t v_offline_boxed_2390_; lean_object* v_res_2391_; 
v_tmp_boxed_2388_ = lean_unbox(v_tmp_2381_);
v_lang_boxed_2389_ = lean_unbox(v_lang_2382_);
v_offline_boxed_2390_ = lean_unbox(v_offline_2385_);
v_res_2391_ = l_Lake_new(v_name_2380_, v_tmp_boxed_2388_, v_lang_boxed_2389_, v_env_2383_, v_cwd_2384_, v_offline_boxed_2390_, v_a_2386_);
return v_res_2391_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1);
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
